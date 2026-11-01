/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.DeRham.Period
public import TauCeti.AlgebraicTopology.Homotopy.Hurewicz.One.Basic

/-!
# Periods of closed `1`-forms on the first singular homology group

A closed `C¹` `1`-form `φ` on a manifold `M` can be integrated along every singular `1`-simplex,
read as a continuous path (`TauCeti.pathClassIntegral`), and hence along every singular
`1`-chain. The integral is additive under concatenation of paths, so it vanishes on the boundaries
of singular `2`-simplices and descends to a homomorphism `TauCeti.homologyPeriodHom φ` from the
first singular homology group `H₁(M; ℤ)` to the coefficients.

Unlike the period homomorphism `TauCeti.periodHom φ x` on the fundamental group, it needs no base
point, and it recovers the periods on loops at every base point: the period homomorphism factors
as `π₁(M, x) → H₁(M; ℤ) → F` through the Hurewicz map (`TauCeti.homologyPeriodHom_hurewicz₁`).
For a path-connected manifold, where the Hurewicz map identifies `H₁(M; ℤ)` with the
abelianization of `π₁(M, x)`, this determines `homologyPeriodHom φ`
(`TauCeti.homologyPeriodHom_hurewiczHomologyAddEquiv`).

For smooth real forms the homomorphism only depends on the de Rham class, and on a connected
manifold it determines the class: `TauCeti.deRhamCohomology.homologyPeriod` is an injective linear
map from `H¹_dR(M)` to the homomorphisms `H₁(M; ℤ) → ℝ`.

The singular chains are those of `TopCat.of M` in `TopCat.{0}`, so `M` and the coefficients live
in `Type`.

## Main declarations

* `TauCeti.homologyPeriodHom φ`: the integral of a closed `C¹` `1`-form on singular `1`-cycles, as
  a homomorphism from `H₁(M; ℤ)` to the coefficients.
* `TauCeti.homologyPeriodHom_homologyπ`: its value on the class of a cycle `Σ nᵢ σᵢ` is
  `Σ nᵢ ∫_{σᵢ} φ`.
* `TauCeti.homologyPeriodHom_hurewicz₁`: the period of a loop is the value on its Hurewicz class.
* `TauCeti.deRhamCohomology.homologyPeriod`: the periods of de Rham classes on `H₁(M; ℤ)`, an
  injective linear map on a connected manifold.

## References

* M. Farber, *Topology of Closed One-Forms*, Section 1.1 (the homomorphism of periods
  `H₁(M; ℤ) → ℝ`).
* Allen Hatcher, *Algebraic Topology*, Theorem 2A.1.
-/

public section

noncomputable section

open CategoryTheory TauCeti.HurewiczOne TauCeti.TopCat
open scoped Manifold ContDiff

namespace TauCeti

variable {E H : Type*} {M F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ E] [T2Space M] [IsManifold I ∞ M] [CompleteSpace F]
  {φ ψ : RoughForm I M F 1}

variable (φ) in
/-- The **period homomorphism on singular homology** of a `1`-form `φ`: the integral of `φ` on
singular `1`-cycles of `M`, as a homomorphism from `H₁(M; ℤ)` to the coefficients. A singular
`1`-simplex is integrated as the continuous path it traces (`TauCeti.pathClassIntegral`). It is
meaningful for closed `C¹` forms, and `0` otherwise. -/
def homologyPeriodHom : ((singularChains ℤ).obj (.of M)).homology 1 →+ F :=
  (H₁.liftPathClass (X := .of M) (f := fun q ↦ pathClassIntegral φ q)
    fun p q ↦ pathClassIntegral_trans p q).comp (H₁AddEquivHomology (.of M)).symm.toAddMonoidHom

/-- The period on the class of a cycle, given in the explicit description `H₁` of the first
homology group. -/
theorem homologyPeriodHom_H₁AddEquivHomology_mk (c : cycles₁ (.of M)) :
    homologyPeriodHom φ (H₁AddEquivHomology (.of M) (H₁.mk c)) =
      chainsDesc (fun s ↦ pathClassIntegral φ (.mk (path₁ s)))
        (c : ((singularChains ℤ).obj (.of M)).X 1) := by
  rw [homologyPeriodHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply, H₁.liftPathClass_mk (fun p q ↦ pathClassIntegral_trans p q)]

/-- The period on the homology class of a cycle `Σ nᵢ σᵢ` is `Σ nᵢ ∫_{σᵢ} φ`. -/
theorem homologyPeriodHom_homologyπ (z : ((singularChains ℤ).obj (.of M)).cycles 1) :
    homologyPeriodHom φ ((((singularChains ℤ).obj (.of M)).homologyπ 1).hom z) =
      chainsDesc (fun s ↦ pathClassIntegral φ (.mk (path₁ s)))
        ((((singularChains ℤ).obj (.of M)).iCycles 1).hom z) := by
  have hz : (((singularChains ℤ).obj (.of M)).iCycles 1).hom z ∈ cycles₁ (.of M) :=
    mem_cycles₁ congr($(((singularChains ℤ).obj (.of M)).iCycles_d 1 0).hom z)
  rw [← H₁AddEquivHomology_mk ⟨_, hz⟩ z rfl, homologyPeriodHom_H₁AddEquivHomology_mk]

/-- The period on the homology class of a loop is the integral along the loop. -/
@[simp]
theorem homologyPeriodHom_loopClass {x : M} (γ : Path x x) :
    homologyPeriodHom φ (H₁AddEquivHomology (.of M) (loopClass (X := .of M) γ)) =
      pathClassIntegral φ (.mk γ) := by
  rw [homologyPeriodHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply, H₁.liftPathClass_loopClass (fun p q ↦ pathClassIntegral_trans p q)]

/-- **The periods factor through `H₁(M; ℤ)`**: the period of a loop class `g` at any base point is
the value of `homologyPeriodHom φ` on the Hurewicz class of `g`. -/
theorem homologyPeriodHom_hurewicz₁ {x : M} (g : FundamentalGroup M x) :
    homologyPeriodHom φ
        (H₁AddEquivHomology (.of M) (Multiplicative.toAdd (hurewicz₁ (.of M) x g))) =
      periodHom φ x (Additive.ofMul g) := by
  obtain ⟨p⟩ := g
  induction p using Path.Homotopic.Quotient.ind with | mk γ =>
  rw [periodHom_apply, toMul_ofMul]
  refine (congrArg (fun h ↦ homologyPeriodHom φ (H₁AddEquivHomology _ (Multiplicative.toAdd h)))
    (hurewicz₁_mk (X := .of M) γ)).trans ?_
  rw [toAdd_ofAdd, homologyPeriodHom_loopClass]

/-- On a path-connected manifold, `homologyPeriodHom φ` is the period homomorphism at `x`
transported along the Hurewicz isomorphism from the abelianization of `π₁(M, x)`. -/
theorem homologyPeriodHom_hurewiczHomologyAddEquiv [PathConnectedSpace M] {x : M}
    (g : FundamentalGroup M x) :
    homologyPeriodHom φ (hurewiczHomologyAddEquiv (X := .of M) x
        (Additive.ofMul (Abelianization.of g))) =
      periodHom φ x (Additive.ofMul g) := by
  rw [hurewiczHomologyAddEquiv_apply, hurewiczAb_ofMul_of, homologyPeriodHom_hurewicz₁]

/-- The periods of a sum of closed `C¹` forms are the sums of their periods. -/
theorem homologyPeriodHom_add (hφ : IsSmoothForm I 1 φ) (hφc : mextDeriv φ = 0)
    (hψ : IsSmoothForm I 1 ψ) (hψc : mextDeriv ψ = 0) :
    homologyPeriodHom (φ + ψ) = homologyPeriodHom φ + homologyPeriodHom ψ := by
  refine homology_one_addMonoidHom_ext fun c ↦ ?_
  rw [AddMonoidHom.add_apply, homologyPeriodHom_H₁AddEquivHomology_mk,
    homologyPeriodHom_H₁AddEquivHomology_mk, homologyPeriodHom_H₁AddEquivHomology_mk,
    ← LinearMap.add_apply]
  refine LinearMap.congr_fun (singularChains_linearMap_ext fun s ↦ ?_) _
  rw [LinearMap.add_apply, chainsDesc_simplexChain_one, chainsDesc_simplexChain_one,
    chainsDesc_simplexChain_one, pathClassIntegral_add hφ hφc hψ hψc]

/-- The periods of a real multiple of a form are the multiples of its periods. -/
@[simp]
theorem homologyPeriodHom_smul (a : ℝ) :
    homologyPeriodHom (a • φ) = a • homologyPeriodHom φ := by
  refine homology_one_addMonoidHom_ext fun c ↦ ?_
  rw [AddMonoidHom.smul_apply, homologyPeriodHom_H₁AddEquivHomology_mk,
    homologyPeriodHom_H₁AddEquivHomology_mk, ← LinearMap.smul_apply]
  refine LinearMap.congr_fun (singularChains_linearMap_ext fun s ↦ ?_) _
  rw [LinearMap.smul_apply, chainsDesc_simplexChain_one, chainsDesc_simplexChain_one,
    pathClassIntegral_smul]

/-- The periods of the zero form vanish. -/
@[simp]
theorem homologyPeriodHom_zero : homologyPeriodHom (0 : RoughForm I M F 1) = 0 := by
  simpa using homologyPeriodHom_smul (φ := (0 : RoughForm I M F 1)) 0

/-! ### Periods of de Rham classes on singular homology -/

/-- Exact smooth real `1`-forms have vanishing periods on singular homology. -/
theorem homologyPeriodHom_eq_zero_of_mem_exactForms {φ : SmoothForm I M ℝ 1}
    (hφ : φ ∈ exactForms I M 1) : homologyPeriodHom (φ : RoughForm I M ℝ 1) = 0 := by
  rw [exactForms_succ, LinearMap.mem_range] at hφ
  obtain ⟨ψ, rfl⟩ := hφ
  -- The integral of `dψ` along a `1`-chain is the evaluation of `ψ` on its boundary.
  have hd : chainsDesc (fun s ↦ pathClassIntegral (mextDerivₗ I 0 ψ : RoughForm I M ℝ 1)
      (.mk (path₁ s))) =
      chainsDesc (fun v ↦ (ψ : RoughForm I M ℝ 0) (_root_.TopCat.toSSetObj₀Equiv v) 0) ∘ₗ
        (((singularChains ℤ).obj (.of M)).d 1 0).hom :=
    singularChains_linearMap_ext fun s ↦ by
      rw [LinearMap.comp_apply, singularChains_d_simplexChain (n := 0), Fin.sum_univ_two,
        map_add, map_zsmul, map_zsmul, chainsDesc_simplexChain_one, chainsDesc_simplexChain_one,
        chainsDesc_simplexChain_one, toSSetObj₀Equiv_δ_zero, toSSetObj₀Equiv_δ_one,
        mextDerivₗ_apply, pathClassIntegral_mextDeriv (ψ.isSmoothForm.of_le (by simp))]
      simp [sub_eq_add_neg]
  refine homology_one_addMonoidHom_ext fun c ↦ ?_
  rw [homologyPeriodHom_H₁AddEquivHomology_mk, AddMonoidHom.zero_apply, hd, LinearMap.comp_apply,
    mem_cycles₁_iff.1 c.2, map_zero]

/-- **Periods on singular homology detect exactness.** A closed smooth real `1`-form on a
connected manifold is exact exactly when its periods on `H₁(M; ℤ)` vanish. -/
theorem mem_exactForms_one_iff_homologyPeriodHom_eq_zero [PreconnectedSpace M]
    {φ : SmoothForm I M ℝ 1} (hφ : φ ∈ closedForms I M 1) :
    φ ∈ exactForms I M 1 ↔ homologyPeriodHom (φ : RoughForm I M ℝ 1) = 0 := by
  refine ⟨homologyPeriodHom_eq_zero_of_mem_exactForms, fun h ↦ ?_⟩
  cases isEmpty_or_nonempty M with
  | inl _ =>
    -- On the empty manifold every form vanishes.
    rw [Subsingleton.elim φ 0]
    exact zero_mem _
  | inr hM =>
  obtain ⟨x⟩ := hM
  rw [mem_exactForms_one_iff_periodHom_eq_zero hφ x]
  refine AddMonoidHom.ext fun g ↦ ?_
  rw [AddMonoidHom.zero_apply, ← ofMul_toMul g, ← homologyPeriodHom_hurewicz₁, h,
    AddMonoidHom.zero_apply]

namespace deRhamCohomology

/-- The periods on singular homology of closed smooth real `1`-forms, as a linear map. -/
private def homologyPeriodClosedForms :
    closedForms I M 1 →ₗ[ℝ] ((singularChains ℤ).obj (.of M)).homology 1 →+ ℝ where
  toFun φ := homologyPeriodHom (φ.1 : RoughForm I M ℝ 1)
  map_add' φ ψ :=
    homologyPeriodHom_add (φ.1.isSmoothForm.of_le (by simp)) ((mem_closedForms I _).mp φ.2)
      (ψ.1.isSmoothForm.of_le (by simp)) ((mem_closedForms I _).mp ψ.2)
  map_smul' a _ := homologyPeriodHom_smul a

/-- Exact forms have vanishing periods on singular homology. -/
private theorem ker_mk_le_ker_homologyPeriodClosedForms :
    LinearMap.ker (mk I (M := M) 1) ≤ LinearMap.ker (homologyPeriodClosedForms (I := I)) := by
  intro φ hφ
  rw [LinearMap.mem_ker, mk_eq_zero_iff] at hφ
  exact homologyPeriodHom_eq_zero_of_mem_exactForms hφ

/-- The **periods of a de Rham class on singular homology** in degree one: the homomorphism
`homologyPeriodHom` of any closed form representing it, as a linear map from `H¹_dR(M)` to the
homomorphisms `H₁(M; ℤ) → ℝ`. -/
def homologyPeriod :
    deRhamCohomology I M 1 →ₗ[ℝ] ((singularChains ℤ).obj (.of M)).homology 1 →+ ℝ :=
  LinearMap.liftOfSurjective (R := ℝ) (M := closedForms I M 1)
    (M₂ := deRhamCohomology I M 1) (M₃ := ((singularChains ℤ).obj (.of M)).homology 1 →+ ℝ)
    (f := mk I (M := M) 1) (mk_surjective I 1)
    ⟨homologyPeriodClosedForms, ker_mk_le_ker_homologyPeriodClosedForms⟩

/-- The periods on singular homology of the class of a closed form are those of the form. -/
@[simp]
theorem homologyPeriod_mk (φ : closedForms I M 1) :
    homologyPeriod (mk I 1 φ) = homologyPeriodHom (φ.1 : RoughForm I M ℝ 1) :=
  LinearMap.equivOfSurjective_apply _ _

/-- The periods of a de Rham class on the Hurewicz class of a loop class `g` are its periods
on `g`. -/
theorem homologyPeriod_hurewicz₁ (c : deRhamCohomology I M 1) {x : M} (g : FundamentalGroup M x) :
    homologyPeriod c
        (H₁AddEquivHomology (.of M) (Multiplicative.toAdd (hurewicz₁ (.of M) x g))) =
      period x c (Additive.ofMul g) := by
  obtain ⟨φ, rfl⟩ := mk_surjective I 1 c
  rw [homologyPeriod_mk, period_mk, homologyPeriodHom_hurewicz₁]

/-- **De Rham classes of degree one are determined by their periods on singular homology** on a
connected manifold. -/
theorem homologyPeriod_injective [PreconnectedSpace M] :
    Function.Injective (homologyPeriod (I := I) (M := M)) := by
  refine (injective_iff_map_eq_zero _).mpr fun c hc ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective I 1 c
  rw [homologyPeriod_mk] at hc
  rw [mk_eq_zero_iff, mem_exactForms_one_iff_homologyPeriodHom_eq_zero φ.2]
  exact hc

end deRhamCohomology

end TauCeti
