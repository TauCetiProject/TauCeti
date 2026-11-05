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

For smooth real forms the homomorphism only depends on the de Rham class, and it determines the
class, with no connectedness assumption: `TauCeti.deRhamCohomology.homologyPeriod` is an injective
linear map from `H¹_dR(M)` to the homomorphisms `H₁(M; ℤ) → ℝ`. A closed form with vanishing periods
has a primitive on each path component, the integral from a base point of the component.

The singular chains are those of `TopCat.of M` in `TopCat.{0}`, so `M` and the coefficients live
in `Type`.

## Main declarations

* `TauCeti.homologyPeriodHom φ`: the integral of a closed `C¹` `1`-form on singular `1`-cycles, as
  a homomorphism from `H₁(M; ℤ)` to the coefficients.
* `TauCeti.homologyPeriodHom_homologyπ`: its value on the class of a cycle `Σ nᵢ σᵢ` is
  `Σ nᵢ ∫_{σᵢ} φ`.
* `TauCeti.homologyPeriodHom_hurewicz₁`: the period of a loop is the value on its Hurewicz class.
* `TauCeti.mem_exactForms_one_iff_homologyPeriodHom_eq_zero`: a closed smooth real `1`-form is
  exact exactly when its periods on `H₁(M; ℤ)` vanish.
* `TauCeti.deRhamCohomology.homologyPeriod`: the periods of de Rham classes on `H₁(M; ℤ)`, an
  injective linear map.

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
@[simp]
theorem homologyPeriodHom_H₁AddEquivHomology_mk (c : cycles₁ (.of M)) :
    homologyPeriodHom φ (H₁AddEquivHomology (.of M) (H₁.mk c)) =
      chainsDesc (fun s ↦ pathClassIntegral φ (.mk (path₁ s)))
        (c : ((singularChains ℤ).obj (.of M)).X 1) := by
  rw [homologyPeriodHom, AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom,
    AddEquiv.symm_apply_apply, H₁.liftPathClass_mk (fun p q ↦ pathClassIntegral_trans p q)]

/-- The period on the homology class of a cycle `Σ nᵢ σᵢ` is `Σ nᵢ ∫_{σᵢ} φ`. -/
@[simp]
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

/-- A homomorphism out of `H₁(M; ℤ)` is `homologyPeriodHom φ` once it is given on the classes of
cycles by a linear map on singular `1`-chains which integrates `φ` along each singular
`1`-simplex. -/
private theorem homologyPeriodHom_eq_of_simplexChain
    {g : ((singularChains ℤ).obj (.of M)).homology 1 →+ F}
    (L : ((singularChains ℤ).obj (.of M)).X 1 →ₗ[ℤ] F)
    (hg : ∀ c : cycles₁ (.of M), g (H₁AddEquivHomology (.of M) (H₁.mk c)) = L c)
    (hL : ∀ s, L (simplexChain s 1) = pathClassIntegral φ (.mk (path₁ s))) :
    homologyPeriodHom φ = g :=
  homology_one_addMonoidHom_ext fun c ↦ by
    rw [homologyPeriodHom_H₁AddEquivHomology_mk, hg]
    refine LinearMap.congr_fun (singularChains_linearMap_ext fun s ↦ ?_) _
    rw [chainsDesc_simplexChain_one, hL]

/-- The periods of a sum of closed `C¹` forms are the sums of their periods. -/
theorem homologyPeriodHom_add (hφ : IsSmoothForm I 1 φ) (hφc : mextDeriv φ = 0)
    (hψ : IsSmoothForm I 1 ψ) (hψc : mextDeriv ψ = 0) :
    homologyPeriodHom (φ + ψ) = homologyPeriodHom φ + homologyPeriodHom ψ :=
  homologyPeriodHom_eq_of_simplexChain (chainsDesc (fun s ↦ pathClassIntegral φ (.mk (path₁ s))) +
      chainsDesc (fun s ↦ pathClassIntegral ψ (.mk (path₁ s))))
    (fun c ↦ by
      rw [AddMonoidHom.add_apply, homologyPeriodHom_H₁AddEquivHomology_mk,
        homologyPeriodHom_H₁AddEquivHomology_mk, LinearMap.add_apply])
    fun s ↦ by
      rw [LinearMap.add_apply, chainsDesc_simplexChain_one, chainsDesc_simplexChain_one,
        pathClassIntegral_add hφ hφc hψ hψc]

/-- The periods of a real multiple of a form are the multiples of its periods. -/
@[simp]
theorem homologyPeriodHom_smul (a : ℝ) :
    homologyPeriodHom (a • φ) = a • homologyPeriodHom φ :=
  homologyPeriodHom_eq_of_simplexChain (a • chainsDesc fun s ↦ pathClassIntegral φ (.mk (path₁ s)))
    (fun c ↦ by
      rw [AddMonoidHom.smul_apply, homologyPeriodHom_H₁AddEquivHomology_mk, LinearMap.smul_apply])
    fun s ↦ by rw [LinearMap.smul_apply, chainsDesc_simplexChain_one, pathClassIntegral_smul]

/-- The periods of a `1`-form which is not a closed `C¹` form are `0` by convention. -/
theorem homologyPeriodHom_undef (h : ¬(IsSmoothForm I 1 φ ∧ mextDeriv φ = 0)) :
    homologyPeriodHom φ = 0 :=
  homology_one_addMonoidHom_ext fun c ↦ by
    rw [homologyPeriodHom_H₁AddEquivHomology_mk, AddMonoidHom.zero_apply]
    refine LinearMap.congr_fun (singularChains_linearMap_ext (L' := 0) fun s ↦ ?_) _
    rw [chainsDesc_simplexChain_one, pathClassIntegral_undef h, LinearMap.zero_apply]

/-- The periods of the zero form vanish. -/
@[simp]
theorem homologyPeriodHom_zero : homologyPeriodHom (0 : RoughForm I M F 1) = 0 := by
  simpa using homologyPeriodHom_smul (φ := (0 : RoughForm I M F 1)) 0

/-- **Stokes' theorem on singular `1`-chains.** The integral of `dψ` along a singular `1`-chain is
the evaluation of the `0`-form `ψ` on its boundary. -/
theorem chainsDesc_pathClassIntegral_mextDeriv {ψ : RoughForm I M F 0} (hψ : IsSmoothForm I 2 ψ) :
    chainsDesc (fun s ↦ pathClassIntegral (mextDeriv ψ) (.mk (path₁ s))) =
      chainsDesc (fun v ↦ ψ (_root_.TopCat.toSSetObj₀Equiv v) 0) ∘ₗ
        (((singularChains ℤ).obj (.of M)).d 1 0).hom :=
  singularChains_linearMap_ext fun s ↦ by
    -- Expand the boundary of `s` into its two vertices and evaluate the chain maps.
    rw [LinearMap.comp_apply, singularChains_d_simplexChain (n := 0), Fin.sum_univ_two]
    simp only [map_add, map_zsmul, chainsDesc_simplexChain_one]
    -- Both sides are the change of `ψ` between the endpoints of `s`.
    rw [toSSetObj₀Equiv_δ_zero, toSSetObj₀Equiv_δ_one, pathClassIntegral_mextDeriv hψ]
    simp [sub_eq_add_neg]

/-! ### Periods of de Rham classes on singular homology -/

/-- Exact smooth real `1`-forms have vanishing periods on singular homology. -/
theorem homologyPeriodHom_eq_zero_of_mem_exactForms {φ : SmoothForm I M ℝ 1}
    (hφ : φ ∈ exactForms I M 1) : homologyPeriodHom (φ : RoughForm I M ℝ 1) = 0 := by
  rw [exactForms_succ, LinearMap.mem_range] at hφ
  obtain ⟨ψ, rfl⟩ := hφ
  refine homology_one_addMonoidHom_ext fun c ↦ ?_
  rw [homologyPeriodHom_H₁AddEquivHomology_mk, AddMonoidHom.zero_apply, mextDerivₗ_apply,
    chainsDesc_pathClassIntegral_mextDeriv (ψ.isSmoothForm.of_le (by simp)), LinearMap.comp_apply,
    mem_cycles₁_iff.1 c.2, map_zero]

/-- Integrals of a form with vanishing periods on singular homology along two paths with the same
endpoints agree. -/
private theorem pathClassIntegral_mk_eq_of_homologyPeriodHom_eq_zero
    (h : homologyPeriodHom φ = 0) {a a' y : M} (e : a = a') (p : Path a y) (q : Path a' y) :
    pathClassIntegral φ (.mk p) = pathClassIntegral φ (.mk q) := by
  subst e
  have hl := homologyPeriodHom_loopClass (φ := φ) (p.trans q.symm)
  rw [h, AddMonoidHom.zero_apply, Path.Homotopic.Quotient.mk_trans,
    Path.Homotopic.Quotient.mk_symm, pathClassIntegral_trans, pathClassIntegral_symm,
    ← sub_eq_add_neg] at hl
  exact sub_eq_zero.mp hl.symm

/-- **Periods on singular homology detect exactness.** A closed smooth real `1`-form is exact
exactly when its periods on `H₁(M; ℤ)` vanish. -/
theorem mem_exactForms_one_iff_homologyPeriodHom_eq_zero {φ : SmoothForm I M ℝ 1}
    (hφ : φ ∈ closedForms I M 1) :
    φ ∈ exactForms I M 1 ↔ homologyPeriodHom (φ : RoughForm I M ℝ 1) = 0 := by
  refine ⟨homologyPeriodHom_eq_zero_of_mem_exactForms, fun h ↦ ?_⟩
  have hφ₁ : IsSmoothForm I 1 (φ : RoughForm I M ℝ 1) := φ.isSmoothForm.of_le (by simp)
  have hclosed := (mem_closedForms I φ).mp hφ
  -- The primitive is the integral from a base point chosen in each path component.
  let b (y : M) : M := (Quotient.mk (pathSetoid M) y).out
  have hb (y : M) : Joined (b y) y := Quotient.mk_out (s := pathSetoid M) y
  set f : M → ℝ := fun y ↦ pathClassIntegral (φ : RoughForm I M ℝ 1) (.mk (hb y).somePath)
  obtain ⟨ψ, hψ, hdψ⟩ := exists_mextDeriv_eq_of_forall_eventuallyEq_add_const
    (r := ((⊤ : ℕ∞) : WithTop ℕ∞)) (by simp) (φ := (φ : RoughForm I M ℝ 1)) (f := f) fun x ↦ by
      -- Near `x`, `f` differs by a constant from a local primitive `g` of `φ`.
      obtain ⟨g, hg, U, hxU, hgU⟩ := exists_contMDiff_isPrimitiveOn (r := ⊤) le_top
        φ.isSmoothForm hclosed x
      refine ⟨g, f x - g x, hg.contMDiffAt, ?_, hgU.mextDeriv_eq x hxU⟩
      filter_upwards [eventually_exists_contMDiff_curve (I := I) (n := 1)
        (hgU.isOpen.mem_nhds hxU)] with y ⟨c, hc, hc₀, hc₁, hcU⟩
      let γ : Path x y :=
        ⟨⟨fun t ↦ c t, hc.continuous.comp continuous_subtype_val⟩, hc₀ 0 le_rfl, hc₁ 1 le_rfl⟩
      have hbxy : b y = b x :=
        (congrArg Quotient.out (Quotient.sound (s := pathSetoid M) ⟨γ⟩)).symm
      simp only [f]
      rw [pathClassIntegral_mk_eq_of_homologyPeriodHom_eq_zero h hbxy (hb y).somePath
          ((hb x).somePath.trans γ), Path.Homotopic.Quotient.mk_trans, pathClassIntegral_trans,
        pathClassIntegral_mk_eq_sub_of_isPrimitiveOn hφ₁ hclosed hgU γ fun t ↦ hcU t]
      abel
  rw [exactForms_succ]
  exact ⟨⟨ψ, hψ.mem_smoothBundleForms⟩, Subtype.ext ((mextDerivₗ_apply I 0 _).trans hdψ)⟩

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

/-- **De Rham classes of degree one are determined by their periods on singular homology.** -/
theorem homologyPeriod_injective :
    Function.Injective (homologyPeriod (I := I) (M := M)) := by
  refine (injective_iff_map_eq_zero _).mpr fun c hc ↦ ?_
  obtain ⟨φ, rfl⟩ := mk_surjective I 1 c
  rw [homologyPeriod_mk] at hc
  rw [mk_eq_zero_iff, mem_exactForms_one_iff_homologyPeriodHom_eq_zero φ.2]
  exact hc

end deRhamCohomology

end TauCeti
