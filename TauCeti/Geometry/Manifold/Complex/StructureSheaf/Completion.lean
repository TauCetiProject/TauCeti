/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Analytic.MultiIndex.TaylorCoeff
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.Germ
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.LocalRing
public import TauCeti.Geometry.Manifold.Complex.StructureSheaf.MaximalIdeal
public import Mathlib.RingTheory.MvPowerSeries.Inverse
public import TauCeti.RingTheory.AdicCompletion.MvPowerSeries
import TauCeti.Data.Finsupp.Interval
import TauCeti.RingTheory.MvPowerSeries.Ideal

/-!
# The completion of a holomorphic stalk is a formal power series ring

Let `𝒪_x` be the ring of germs at `x` of holomorphic functions on `ℂ^ι`, for a finite type `ι`,
and let `𝔪` be its maximal ideal, the germs vanishing at `x`. The Taylor series at `x` is a ring
homomorphism `taylorSeries x : 𝒪_x →+* ℂ⟦z_i⟧`, in the centred coordinates `z i - x i`. It is
injective by the identity theorem, but not surjective: a formal power series need not converge.

Modulo the powers of `𝔪`, the Taylor series is an isomorphism. A germ lies in `𝔪 ^ n` exactly when
its Taylor coefficients of total degree below `n` vanish, and every polynomial of degree below `n`
is a Taylor polynomial. Hence the `𝔪`-adic completion of `𝒪_x` is the formal power series ring
`ℂ⟦z_i⟧`, compatibly with the Taylor series. This is the analytic half of the comparison of the
completed local rings of a complex algebraic variety and of its analytification.

The analytic input is that the centred coordinate germs generate `𝔪`, by Hadamard's lemma
(`OpenPartialHomeomorph.ker_eval_eq_span_holomorphicLinearCoordinateGerm`), together with the
multiplicativity of Taylor coefficients (`AnalyticAt.mvTaylorCoeff_mul`). The rest is the
algebraic comparison `TauCeti.adicCompletionEquivMvPowerSeries`.

## Main definitions and results

* `TauCeti.holomorphicStructureSheaf.taylorSeries`: the Taylor series of holomorphic germs, with
  coefficients `TauCeti.holomorphicStructureSheaf.coeff_taylorSeries` and constant term the value
  at `x` (`TauCeti.holomorphicStructureSheaf.constantCoeff_taylorSeries`). It sends constant germs
  to constants (`TauCeti.holomorphicStructureSheaf.taylorSeries_germ_algebraMap`) and the centred
  coordinate germs to the variables
  (`TauCeti.holomorphicStructureSheaf.taylorSeries_holomorphicLinearCoordinateGerm_basisFun`).
* `TauCeti.holomorphicStructureSheaf.span_range_holomorphicLinearCoordinateGerm_basisFun`: the
  centred coordinate germs generate the maximal ideal of the stalk.
* `TauCeti.holomorphicStructureSheaf.taylorSeries_injective`: a germ is determined by its
  Taylor series.
* `TauCeti.holomorphicStructureSheaf.comap_taylorSeries_maximalIdeal_pow`: the germs whose Taylor
  series has order at least `n` are those of `𝔪 ^ n`; in terms of a representative,
  `TauCeti.holomorphicStructureSheaf.mem_maximalIdeal_pow_iff_mvTaylorCoeff_eq_zero`.
* `TauCeti.holomorphicStructureSheaf.adicCompletionEquiv`: the `𝔪`-adic completion of `𝒪_x` is
  `ℂ⟦z_i⟧`, extending the Taylor series
  (`TauCeti.holomorphicStructureSheaf.adicCompletionEquiv_of`) and inducing it modulo every power
  of `𝔪` (`TauCeti.holomorphicStructureSheaf.mk_adicCompletionEquiv`).

## References

* A. Grothendieck et al., *Revêtements étales et groupe fondamental* (SGA 1), Exposé XII,
  Théorème et définition 1.1 and its proof.
* R. C. Gunning and H. Rossi, *Analytic Functions of Several Complex Variables*, Chapter II.
-/

public noncomputable section

open CategoryTheory Filter Topology MvPowerSeries
open scoped ContDiff Manifold

namespace TauCeti.holomorphicStructureSheaf

variable {ι : Type} [Fintype ι] (x : ι → ℂ)

/-- The power series whose coefficients are the Taylor coefficients at `x` of any representative of
a germ of functions. -/
private def germTaylorSeries (g : Germ (𝓝 x) ℂ) : MvPowerSeries ι ℂ :=
  fun α ↦ g.liftOn (fun φ ↦ mvTaylorCoeff φ x α) fun _ _ h ↦ h.mvTaylorCoeff_eq α

private theorem coeff_germTaylorSeries (φ : (ι → ℂ) → ℂ) (α : ι →₀ ℕ) :
    coeff α (germTaylorSeries x (φ : Germ (𝓝 x) ℂ)) = mvTaylorCoeff φ x α :=
  coeff_apply _ _

/-- The **Taylor series** at `x` of a holomorphic germ at `x` on `ℂ^ι`: the formal power series in
the centred coordinates `z i - x i` whose coefficients are the multi-index Taylor coefficients at
`x` of any representative (`coeff_taylorSeries`). -/
def taylorSeries :
    (holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.stalk x →+* MvPowerSeries ι ℂ where
  toFun s := germTaylorSeries x (toFilterGerm 𝓘(ℂ, ι → ℂ) (ι → ℂ) x (𝓝 x) le_rfl s)
  map_one' := by
    classical
    ext α
    rw [map_one, ← Germ.coe_one, coeff_germTaylorSeries, mvTaylorCoeff_one, coeff_one]
    simp only [Finsupp.coe_eq_zero]
  map_mul' s t := by
    classical
    obtain ⟨φ, hφ, hs⟩ := exists_analyticAt_toFilterGerm_eq x s
    obtain ⟨ψ, hψ, ht⟩ := exists_analyticAt_toFilterGerm_eq x t
    ext α
    rw [map_mul, hs, ht, ← Germ.coe_mul, coeff_germTaylorSeries, hφ.mvTaylorCoeff_mul hψ,
      coeff_mul]
    simp only [coeff_germTaylorSeries]
    exact (Finsupp.sum_antidiagonal_eq_sum_Iic_coe
      (fun β γ ↦ mvTaylorCoeff φ x β * mvTaylorCoeff ψ x γ) α).symm
  map_zero' := by
    ext α
    rw [map_zero, ← Germ.coe_zero, coeff_germTaylorSeries, mvTaylorCoeff_zero, map_zero]
  map_add' s t := by
    obtain ⟨φ, hφ, hs⟩ := exists_analyticAt_toFilterGerm_eq x s
    obtain ⟨ψ, hψ, ht⟩ := exists_analyticAt_toFilterGerm_eq x t
    ext α
    rw [map_add, hs, ht, ← Germ.coe_add, map_add, coeff_germTaylorSeries, coeff_germTaylorSeries,
      coeff_germTaylorSeries, hφ.mvTaylorCoeff_add hψ]

private theorem taylorSeries_apply
    (s : (holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.stalk x) :
    taylorSeries x s = germTaylorSeries x (toFilterGerm 𝓘(ℂ, ι → ℂ) (ι → ℂ) x (𝓝 x) le_rfl s) :=
  rfl

variable {x} in
/-- The coefficients of the Taylor series of a holomorphic germ are the Taylor coefficients of any
function with the same germ. -/
theorem coeff_taylorSeries {s : (holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.stalk x}
    {φ : (ι → ℂ) → ℂ}
    (h : toFilterGerm 𝓘(ℂ, ι → ℂ) (ι → ℂ) x (𝓝 x) le_rfl s = φ) (α : ι →₀ ℕ) :
    coeff α (taylorSeries x s) = mvTaylorCoeff φ x α := by
  rw [taylorSeries_apply, h, coeff_germTaylorSeries]

/-- The constant term of the Taylor series of a holomorphic germ is its value at `x`. -/
@[simp]
theorem constantCoeff_taylorSeries
    (s : (holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.stalk x) :
    constantCoeff (taylorSeries x s) = eval 𝓘(ℂ, ι → ℂ) (ι → ℂ) x s := by
  obtain ⟨φ, hφ, hs⟩ := exists_analyticAt_toFilterGerm_eq x s
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_taylorSeries (hs _ le_rfl),
    eval_eq_of_toFilterGerm_eq (hs _ le_rfl)]
  exact hφ.mvTaylorCoeff_zero

/-- The Taylor series of the germ of a globally holomorphic function has its Taylor coefficients. -/
@[simp]
theorem coeff_taylorSeries_germOfContMDiff (φ : (ι → ℂ) → ℂ)
    (hφ : ContMDiff 𝓘(ℂ, ι → ℂ) 𝓘(ℂ) ω φ) (α : ι →₀ ℕ) :
    coeff α (taylorSeries x (germOfContMDiff φ hφ x)) = mvTaylorCoeff φ x α :=
  coeff_taylorSeries (toFilterGerm_germOfContMDiff φ hφ le_rfl) α

/-- **Identity theorem**: a holomorphic germ is determined by its Taylor series. -/
theorem taylorSeries_injective : Function.Injective (taylorSeries x) := by
  intro s t hst
  obtain ⟨φ, hφ, hs⟩ := exists_analyticAt_toFilterGerm_eq x s
  obtain ⟨ψ, hψ, ht⟩ := exists_analyticAt_toFilterGerm_eq x t
  refine toFilterGerm_nhds_injective x ?_
  rw [hs _ le_rfl, ht _ le_rfl, Germ.coe_eq, hφ.eventuallyEq_iff_forall_mvTaylorCoeff_eq hψ]
  intro α
  simpa [coeff_taylorSeries (hs _ le_rfl), coeff_taylorSeries (ht _ le_rfl)] using
    congr(coeff (Finsupp.equivFunOnFinite.symm α) $hst)

/-! ### Comparison with the formal power series ring -/

/-- The constant germs. -/
private def constGerm : ℂ →+* (holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.stalk x :=
  (ConcreteCategory.hom ((holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.germ ⊤ x
    trivial)).comp (algebraMap ℂ _)

private theorem toFilterGerm_constGerm (r : ℂ) :
    toFilterGerm 𝓘(ℂ, ι → ℂ) (ι → ℂ) x (𝓝 x) le_rfl (constGerm x r) = (fun _ ↦ r : (ι → ℂ) → ℂ) :=
  toFilterGerm_germ le_rfl trivial _ _ fun _ ↦ algebraMap_apply _ r _

private theorem taylorSeries_comp_constGerm : (taylorSeries x).comp (constGerm x) = C := by
  classical
  ext r α
  rw [RingHom.comp_apply, coeff_taylorSeries (toFilterGerm_constGerm x r), mvTaylorCoeff_const,
    coeff_C]
  simp only [Finsupp.coe_eq_zero]

/-- The Taylor series of a constant germ is the constant power series. -/
@[simp]
theorem taylorSeries_germ_algebraMap (r : ℂ) :
    taylorSeries x ((holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.germ ⊤ x trivial
      (algebraMap ℂ _ r)) = C r :=
  RingHom.congr_fun (taylorSeries_comp_constGerm x) r

private theorem eval_constGerm (r : ℂ) : eval 𝓘(ℂ, ι → ℂ) (ι → ℂ) x (constGerm x r) = r :=
  eval_eq_of_toFilterGerm_eq (toFilterGerm_constGerm x r)

/-- The Taylor series of the centred coordinate germ `y ↦ y i - x i` is the variable `X i`. -/
@[simp]
theorem taylorSeries_holomorphicLinearCoordinateGerm_basisFun (i : ι) :
    taylorSeries x ((OpenPartialHomeomorph.refl (ι → ℂ)).holomorphicLinearCoordinateGerm
      (StructureGroupoid.id_mem_maximalAtlas _) x
      (LinearMap.toContinuousLinearMap ((Pi.basisFun ℂ ι).coord i)) (Set.mem_univ x)) = X i := by
  classical
  have h : (fun y : ι → ℂ ↦ ∏ j, (y j - x j) ^ (Pi.single i 1 : ι → ℕ) j) =
      fun y ↦ LinearMap.toContinuousLinearMap ((Pi.basisFun ℂ ι).coord i)
        (OpenPartialHomeomorph.refl (ι → ℂ) y - OpenPartialHomeomorph.refl (ι → ℂ) x) := by
    ext y
    rw [Fintype.prod_eq_single i fun j hj ↦ by simp [Pi.single_eq_of_ne hj]]
    simp
  ext α
  refine (coeff_taylorSeries (α := α)
    (OpenPartialHomeomorph.toFilterGerm_holomorphicLinearCoordinateGerm _ _ _ _ _ le_rfl)).trans ?_
  rw [← h, mvTaylorCoeff_prod_sub_pow, coeff_X, ← Finsupp.single_eq_pi_single]
  simp only [DFunLike.coe_fn_eq]

/-- The centred coordinate germs `y ↦ y i - x i` generate the maximal ideal of the stalk at `x`. -/
theorem span_range_holomorphicLinearCoordinateGerm_basisFun :
    Ideal.span (Set.range fun i ↦
      (OpenPartialHomeomorph.refl (ι → ℂ)).holomorphicLinearCoordinateGerm
        (StructureGroupoid.id_mem_maximalAtlas _) x
        (LinearMap.toContinuousLinearMap ((Pi.basisFun ℂ ι).coord i)) (Set.mem_univ x)) =
      IsLocalRing.maximalIdeal
        ((holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.stalk x) := by
  rw [maximalIdeal_stalk, OpenPartialHomeomorph.ker_eval_eq_span_holomorphicLinearCoordinateGerm
    (OpenPartialHomeomorph.refl (ι → ℂ)) (StructureGroupoid.id_mem_maximalAtlas _)
    (Pi.basisFun ℂ ι) (Set.mem_univ x)]

private theorem mk_maximalIdeal_comp_constGerm_surjective :
    Function.Surjective ((Ideal.Quotient.mk (IsLocalRing.maximalIdeal
      ((holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.stalk x))).comp (constGerm x)) := by
  intro y
  obtain ⟨s, rfl⟩ := Ideal.Quotient.mk_surjective y
  refine ⟨eval 𝓘(ℂ, ι → ℂ) (ι → ℂ) x s, Ideal.Quotient.eq.2 ?_⟩
  rw [maximalIdeal_stalk, RingHom.mem_ker, map_sub, eval_constGerm, sub_self]

/-- **Taylor series and powers of the maximal ideal.** A holomorphic germ at `x` lies in the
`n`-th power of the maximal ideal exactly when its Taylor series lies in the `n`-th power of the
maximal ideal of `ℂ⟦z_i⟧`, that is, has order at least `n`. -/
theorem comap_taylorSeries_maximalIdeal_pow (n : ℕ) :
    (IsLocalRing.maximalIdeal (MvPowerSeries ι ℂ) ^ n).comap (taylorSeries x) =
      IsLocalRing.maximalIdeal
        ((holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.stalk x) ^ n := by
  rw [maximalIdeal_eq_span_range_X]
  exact comap_pow_span_range_X (taylorSeries_comp_constGerm x)
    (taylorSeries_holomorphicLinearCoordinateGerm_basisFun x)
    (span_range_holomorphicLinearCoordinateGerm_basisFun x)
    (mk_maximalIdeal_comp_constGerm_surjective x) n

variable {x} in
/-- A holomorphic germ at `x` lies in the `n`-th power of the maximal ideal exactly when the Taylor
coefficients at `x` of total degree below `n` of any representative vanish. -/
theorem mem_maximalIdeal_pow_iff_mvTaylorCoeff_eq_zero
    {s : (holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.stalk x}
    {φ : (ι → ℂ) → ℂ}
    (h : toFilterGerm 𝓘(ℂ, ι → ℂ) (ι → ℂ) x (𝓝 x) le_rfl s = φ) {n : ℕ} :
    s ∈ IsLocalRing.maximalIdeal
        ((holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.stalk x) ^ n ↔
      ∀ α : ι → ℕ, ∑ i, α i < n → mvTaylorCoeff φ x α = 0 := by
  rw [← comap_taylorSeries_maximalIdeal_pow, Ideal.mem_comap, mem_maximalIdeal_pow_iff_le_order]
  refine ⟨fun h' α hα ↦ ?_, fun h' ↦ nat_le_order fun d hd ↦ ?_⟩
  · have := coeff_of_lt_order (d := Finsupp.equivFunOnFinite.symm α)
      ((Nat.cast_lt.2 (by simpa [Finsupp.degree_eq_sum] using hα)).trans_le h')
    simpa [coeff_taylorSeries h] using this
  · rw [coeff_taylorSeries h]
    exact h' d (by simpa [Finsupp.degree_eq_sum] using hd)

/-- **The completed holomorphic stalk.** The completion of the ring of holomorphic germs at `x`
on `ℂ^ι` at its maximal ideal is the formal power series ring `ℂ⟦z_i⟧`, compatibly with the Taylor
series (`adicCompletionEquiv_of`). -/
def adicCompletionEquiv :
    AdicCompletion
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.stalk x))
      ((holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.stalk x) ≃+* MvPowerSeries ι ℂ :=
  adicCompletionEquivMvPowerSeries (taylorSeries_comp_constGerm x)
    (taylorSeries_holomorphicLinearCoordinateGerm_basisFun x)
    (span_range_holomorphicLinearCoordinateGerm_basisFun x)
    (mk_maximalIdeal_comp_constGerm_surjective x)

/-- The completion isomorphism `adicCompletionEquiv` extends the Taylor series. -/
@[simp]
theorem adicCompletionEquiv_of
    (s : (holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.stalk x) :
    adicCompletionEquiv x (AdicCompletion.of _ _ s) = taylorSeries x s :=
  adicCompletionEquivMvPowerSeries_of _ _ _ _ s

/-- Modulo the `n`-th power of the maximal ideal, the completion isomorphism `adicCompletionEquiv`
is the isomorphism of quotients induced by the Taylor series. -/
@[simp]
theorem mk_adicCompletionEquiv (n : ℕ)
    (y : AdicCompletion
      (IsLocalRing.maximalIdeal ((holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.stalk x))
      ((holomorphicStructureSheaf 𝓘(ℂ, ι → ℂ) (ι → ℂ)).presheaf.stalk x)) :
    Ideal.Quotient.mk (IsLocalRing.maximalIdeal (MvPowerSeries ι ℂ) ^ n) (adicCompletionEquiv x y) =
      Ideal.quotientMap _ (taylorSeries x) (comap_taylorSeries_maximalIdeal_pow x n).ge
        (AdicCompletion.evalₐ _ n y) := by
  obtain ⟨s, hs⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ _ n y)
  have h := mk_adicCompletionEquivMvPowerSeries (taylorSeries_comp_constGerm x)
    (taylorSeries_holomorphicLinearCoordinateGerm_basisFun x)
    (span_range_holomorphicLinearCoordinateGerm_basisFun x)
    (mk_maximalIdeal_comp_constGerm_surjective x) n y
  rw [← hs, Ideal.quotientMap_mk, Ideal.Quotient.eq] at h ⊢
  rwa [maximalIdeal_eq_span_range_X]

end TauCeti.holomorphicStructureSheaf
