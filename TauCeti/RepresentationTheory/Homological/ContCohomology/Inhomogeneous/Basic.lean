/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Homological.ContCohomology.Resolution.Evaluation
public import TauCeti.Topology.Algebra.Monoid

/-!
# The complex of continuous inhomogeneous cochains

Let `X` be a topological representation of a topological group `G` whose action map
`G × X → X` is jointly continuous. Its continuous inhomogeneous `n`-cochains are the continuous
functions `C(Gⁿ, X)`, with the classical differential

```text
(d f)(g₀, …, gₙ) = g₀ • f (g₁, …, gₙ) + ∑ⱼ (-1)ʲ⁺¹ f (g₀, …, gⱼ gⱼ₊₁, …, gₙ),
```

the sum running over `j = 0, …, n`, where the term `j = n` is `(-1)ⁿ⁺¹ f (g₀, …, gₙ₋₁)`. This file
builds the complex `TopRep.continuousInhomogeneousCochains X hX` of `k`-modules, with no
compactness or discreteness assumed of the coefficients. Joint continuity of the action is what
keeps `d f` continuous; continuity of each operator separately, as in `TopRep`, is not enough.

The relation `d ∘ d = 0` is not proved by hand. A continuous cochain `f` has a homogeneous partner
`TopRep.homogenization X hX n f`, the invariant element of the coinduced resolution with values
`x ↦ x₀ • f (x₀⁻¹ x₁, …, xₙ₋₁⁻¹ xₙ)`, and `f` is recovered from the values of its partner at the
partial products `(1, g₀, g₀ g₁, …)` of a tuple
(`TopRep.resolutionEval_homogenization_partialProd`).
Reading the differential of the resolution at partial products gives the inhomogeneous
differential (`TopRep.resolutionEval_d_partialProd`), so `d ∘ d = 0` is inherited from Mathlib's
coinduced resolution. The same two facts identify the complex with Mathlib's homogeneous cochains
over a locally compact group, in
`TauCeti.RepresentationTheory.Homological.ContCohomology.Inhomogeneous.Comparison`.

The formulas follow Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, 2nd ed., Chapter I
§2, and the identification of the homogeneous and inhomogeneous descriptions follows the proof for
discrete groups behind Mathlib's `groupCohomology.inhomogeneousCochainsIso`, through
`Fin.partialProd` and `Fin.partialProd_contractNth`.

## Main definitions

* `TopRep.continuousInhomogeneousCochainsD`: the inhomogeneous differential on continuous
  cochains.
* `TopRep.continuousInhomogeneousCochains`: the complex of continuous inhomogeneous cochains.
* `TopRep.homogenization`: the homogeneous partner of a continuous inhomogeneous cochain.

## Main results

* `TopRep.continuousInhomogeneousCochains_d_apply`: the differential of the complex, at a point.
* `TopRep.resolutionEval_d_partialProd`: at partial products, the differential of an invariant
  element of the coinduced resolution is the inhomogeneous differential of its values.
-/

public section

namespace TopRep

open CategoryTheory

universe u v w

variable {k : Type u} {G : Type v} [Ring k] [TopologicalSpace k] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {X : TopRep.{max v w} k G}

variable (X) in
/-- The inhomogeneous differential `C(Gⁿ, X) → C(Gⁿ⁺¹, X)`,
`(d f)(g₀, …, gₙ) = g₀ • f (g₁, …, gₙ) + ∑ⱼ (-1)ʲ⁺¹ f (g₀, …, gⱼ gⱼ₊₁, …, gₙ)`, of a representation
whose action map `G × X → X` is jointly continuous. -/
noncomputable def continuousInhomogeneousCochainsD
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    C(Fin n → G, X.V) →ₗ[k] C(Fin (n + 1) → G, X.V) where
  toFun f :=
    { toFun g := X.ρ (g 0) (f (Fin.tail g)) +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g)
      continuous_toFun := by
        have h₀ : Continuous fun g : Fin (n + 1) → G ↦ (g 0, f (Fin.tail g)) := by fun_prop
        exact (hX.comp h₀).add <| continuous_finsetSum _ fun j _ ↦
          (f.continuous.comp (continuous_id.finContractNth j)).const_smul
            ((-1 : ℤ) ^ ((j : ℕ) + 1)) }
  map_add' f f' := by
    ext g
    simp [Finset.sum_add_distrib, add_add_add_comm]
  map_smul' c f := by
    ext g
    simp [Finset.smul_sum, smul_comm _ c]

@[simp]
theorem continuousInhomogeneousCochainsD_apply (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (n : ℕ) (f : C(Fin n → G, X.V)) (g : Fin (n + 1) → G) :
    continuousInhomogeneousCochainsD X hX n f g = X.ρ (g 0) (f (Fin.tail g)) +
      ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) :=
  (rfl)

/-- **The differential at partial products is the inhomogeneous differential.** Let `F` be a
`G`-invariant element of the `(n + 1)`-st term of the coinduced resolution, that is, a homogeneous
`n`-cochain, whose values at the partial products `(1, g₀, g₀ g₁, …)` form the continuous
inhomogeneous cochain `f`. Then the values of `d F` at partial products form `d f`. -/
theorem resolutionEval_d_partialProd (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) {n : ℕ}
    {F : (resolutionX X (n + 1)).V} (hF : ∀ g, (resolutionX X (n + 1)).ρ g F = F)
    {f : C(Fin n → G, X.V)} (hf : ∀ g, resolutionEval X (n + 1) F (Fin.partialProd g) = f g)
    (g : Fin (n + 1) → G) :
    resolutionEval X (n + 2) ((d X (n + 1)).hom F) (Fin.partialProd g) =
      continuousInhomogeneousCochainsD X hX n f g := by
  rw [resolutionEval_d_apply, Fin.sum_univ_succ, continuousInhomogeneousCochainsD_apply]
  congr 1
  · have h0 : Fin.partialProd g ∘ (0 : Fin (n + 2)).succAbove =
        fun i ↦ g 0 * Fin.partialProd (Fin.tail g) i := by
      ext i
      simp [Fin.partialProd_succ', Fin.tail_def]
    rw [h0, resolutionEval_mul_left_of_forall_ρ_eq hF, hf]
    simp
  · refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← Fin.partialProd_contractNth, hf, Fin.val_succ]

variable (X) in
/-- The homogeneous partner `x ↦ x₀ • f (x₀⁻¹ x₁, …, xₙ₋₁⁻¹ xₙ)` of a continuous function `f` on
`Gⁿ`, as a continuous function on `Gⁿ⁺¹`. -/
private noncomputable def homogenizationFun (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (n : ℕ) (f : C(Fin n → G, X.V)) : C(Fin (n + 1) → G, X.V) where
  toFun x := X.ρ (x 0) (f fun i ↦ (x i.castSucc)⁻¹ * x i.succ)
  continuous_toFun := by
    have h₀ : Continuous fun x : Fin (n + 1) → G ↦
        (x 0, f fun i ↦ (x i.castSucc)⁻¹ * x i.succ) := by fun_prop
    exact hX.comp h₀

variable (X) in
/-- The homogeneous partner of a continuous inhomogeneous `n`-cochain `f`: the element of the
`(n + 1)`-st term of the coinduced resolution with values `x ↦ x₀ • f (x₀⁻¹ x₁, …, xₙ₋₁⁻¹ xₙ)`
(`TopRep.resolutionEval_homogenization`). It is `G`-invariant (`TopRep.ρ_homogenization`), that is,
a homogeneous cochain. -/
noncomputable def homogenization (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ)
    (f : C(Fin n → G, X.V)) : (resolutionX X (n + 1)).V :=
  resolutionCurry X (n + 1) (homogenizationFun X hX n f)

/-- The values of the homogeneous partner: `x ↦ x₀ • f (x₀⁻¹ x₁, …, xₙ₋₁⁻¹ xₙ)`. -/
theorem resolutionEval_homogenization (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ)
    (f : C(Fin n → G, X.V)) (x : Fin (n + 1) → G) :
    resolutionEval X (n + 1) (homogenization X hX n f) x =
      X.ρ (x 0) (f fun i ↦ (x i.castSucc)⁻¹ * x i.succ) :=
  congrFun (resolutionEval_resolutionCurry X (n + 1) (homogenizationFun X hX n f)) x

/-- The homogeneous partner of a continuous inhomogeneous cochain is `G`-invariant. -/
theorem ρ_homogenization (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ)
    (f : C(Fin n → G, X.V)) (g : G) :
    (resolutionX X (n + 1)).ρ g (homogenization X hX n f) = homogenization X hX n f := by
  refine resolutionEval_injective X (n + 1) (funext fun x ↦ ?_)
  rw [resolutionEval_ρ_apply, resolutionEval_homogenization, resolutionEval_homogenization,
    ← mul_apply_eq_comp, ← map_mul]
  simp [mul_assoc]

/-- A continuous inhomogeneous cochain is the restriction of its homogeneous partner to the
partial products `(1, g₀, g₀ g₁, …)`. -/
theorem resolutionEval_homogenization_partialProd
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) (f : C(Fin n → G, X.V))
    (g : Fin n → G) :
    resolutionEval X (n + 1) (homogenization X hX n f) (Fin.partialProd g) = f g := by
  rw [resolutionEval_homogenization]
  simp [Fin.partialProd_right_inv]

/-- The inhomogeneous differential squares to zero. -/
theorem continuousInhomogeneousCochainsD_comp_eq_zero
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (n : ℕ) :
    continuousInhomogeneousCochainsD X hX (n + 1) ∘ₗ continuousInhomogeneousCochainsD X hX n =
      0 := by
  ext f g
  set F := homogenization X hX n f
  have hF : ∀ h, (resolutionX X (n + 1)).ρ h F = F := ρ_homogenization hX n f
  have hdF : ∀ h, (resolutionX X (n + 2)).ρ h ((d X (n + 1)).hom F) = (d X (n + 1)).hom F :=
    fun h ↦ by rw [← ContIntertwiningMap.isIntertwining, hF]
  have h₁ := resolutionEval_d_partialProd hX hF (resolutionEval_homogenization_partialProd hX n f)
  have h₂ := resolutionEval_d_partialProd hX hdF h₁ g
  have h0 : (d X (n + 2)).hom ((d X (n + 1)).hom F) = 0 := by
    have := congrArg (fun φ ↦ φ.hom F) (d_comp_d X (n + 1))
    simp only [hom_comp, hom_zero] at this
    exact this
  rw [h0, map_zero] at h₂
  exact h₂.symm

variable (X) in
/-- **The complex of continuous inhomogeneous cochains** `C(G⁰, X) → C(G¹, X) → C(G², X) → ⋯`
of a representation whose action map `G × X → X` is jointly continuous, with the inhomogeneous
differential `TopRep.continuousInhomogeneousCochainsD`. -/
noncomputable abbrev continuousInhomogeneousCochains
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) : CochainComplex (ModuleCat.{max v w} k) ℕ :=
  CochainComplex.of (fun n ↦ ModuleCat.of k C(Fin n → G, X.V))
    (fun n ↦ ModuleCat.ofHom (continuousInhomogeneousCochainsD X hX n))
    fun n ↦ by
      ext1
      exact continuousInhomogeneousCochainsD_comp_eq_zero hX n

/-- The differential of the complex of continuous inhomogeneous cochains, at a point:
`(d f)(g₀, …, gₙ) = g₀ • f (g₁, …, gₙ) + ∑ⱼ (-1)ʲ⁺¹ f (g₀, …, gⱼ gⱼ₊₁, …, gₙ)`. -/
theorem continuousInhomogeneousCochains_d_apply (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2)
    (n : ℕ) (f : C(Fin n → G, X.V)) (g : Fin (n + 1) → G) :
    ((continuousInhomogeneousCochains X hX).d n (n + 1)).hom f g =
      X.ρ (g 0) (f (Fin.tail g)) +
        ∑ j : Fin (n + 1), (-1 : ℤ) ^ ((j : ℕ) + 1) • f (Fin.contractNth j (· * ·) g) := by
  simp [continuousInhomogeneousCochains]

/-- The differential in degree zero: `(d m) g = g • m - m`, where the `0`-cochain `f` is the
element `m = f ()`. -/
theorem continuousInhomogeneousCochains_d_zero_apply
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (f : C(Fin 0 → G, X.V)) (g : Fin 1 → G) :
    ((continuousInhomogeneousCochains X hX).d 0 1).hom f g =
      X.ρ (g 0) (f Fin.elim0) - f Fin.elim0 := by
  rw [continuousInhomogeneousCochains_d_apply, Fin.sum_univ_one,
    Subsingleton.elim (Fin.tail g) Fin.elim0, Subsingleton.elim (Fin.contractNth _ _ g) Fin.elim0]
  simp [sub_eq_add_neg]

/-- The differential in degree one: `(d f) (g, h) = g • f h - f (g h) + f g`, writing a
`1`-cochain `f` as a function of one group element. -/
theorem continuousInhomogeneousCochains_d_one_apply
    (hX : Continuous fun p : G × X.V ↦ X.ρ p.1 p.2) (f : C(Fin 1 → G, X.V)) (g : Fin 2 → G) :
    ((continuousInhomogeneousCochains X hX).d 1 2).hom f g =
      X.ρ (g 0) (f fun _ ↦ g 1) - f (fun _ ↦ g 0 * g 1) + f fun _ ↦ g 0 := by
  rw [continuousInhomogeneousCochains_d_apply, Fin.sum_univ_two]
  have h₀ : Fin.contractNth 0 (· * ·) g = fun _ ↦ g 0 * g 1 := by
    ext i
    fin_cases i
    simp [Fin.contractNth]
  have h₁ : Fin.contractNth 1 (· * ·) g = fun _ ↦ g 0 := by
    ext i
    fin_cases i
    simp [Fin.contractNth]
  have h₂ : Fin.tail g = fun _ ↦ g 1 := by
    ext i
    fin_cases i
    rfl
  simp [h₀, h₁, h₂, sub_eq_add_neg, add_assoc]

end TopRep
