/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.CompactSupport
import TauCeti.Analysis.Calculus.BumpFunction.Cutoff
import TauCeti.Analysis.Calculus.IteratedFDeriv.Basic
import TauCeti.Analysis.Calculus.IteratedFDeriv.Lp
import TauCeti.Analysis.Holder.MeanValue
import TauCeti.Analysis.InnerProductSpace.Orthonormal.Multilinear
import TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Cutoff
import TauCeti.Topology.MetricSpace.Bounded

/-!
# The interior Schauder estimate on small balls

Let `0 < α < 1`, and let `L u = ∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼu` be a non-divergence-form operator on `ℝ^{n+1}`
whose coefficients are `α`-Hölder with constant `L` on the closed ball `closedBall x₀ R`, and such
that `a(x₀)` has ellipticity constants `0 < λ ≤ Λ`. If `R` is small compared with the Hölder
modulus of the coefficients, in the sense of the scale condition of
`TauCeti.PDE.exists_holderWith_iteratedFDeriv_two_of_support_subset_closedBall`, then for every
`ρ < R` there is a constant `C`, independent of the solution, such that every `u` which is `C²` on
the open ball `B_R` with `α`-Hölder Hessian there satisfies

`[D²u]_{α; closedBall x₀ ρ} ≤ C ([L u]_{α; B_R} + N)`,

where `N` bounds `|u|`, `‖Du‖` and `‖D²u‖` on `B_R`. The Hölder constant of the Hessian on `B_R`
enters only qualitatively: the estimate does not depend on it. The constant `C` depends on the
coefficients only through `λ`, `Λ`, `L` and a bound `M` for their entries on the ball, and not on
the centre `x₀`. This is the localized form of the Schauder estimate used to pass from
coefficients of small oscillation on a ball to Hölder continuous coefficients, by covering a
compact set with finitely many small balls, or the whole space with balls of one radius.

## The argument

Choose a smooth cutoff `ζ` equal to one near `closedBall x₀ ρ` with support in `B_R`, the
translate of one fixed cutoff about the origin so that its bounds do not depend on `x₀`, and put
`w = ζ u`, which is `C²` on the whole space (`ContDiffOn.contDiff_smul_of_tsupport_subset`). By the
second-order product rule (see `TauCeti.Analysis.PDE.Regularity.Hessian.Schauder.Cutoff`),

`∂ᵢ∂ⱼw = ζ ∂ᵢ∂ⱼu + Tᵢⱼ`, where `Tᵢⱼ = u ∂ᵢ∂ⱼζ + ∂ᵢζ ∂ⱼu + ∂ⱼζ ∂ᵢu`,

so `L w = ζ L u + ∑ᵢⱼ aᵢⱼ Tᵢⱼ`. Every term is a product of a globally Hölder factor built from
`ζ`, vanishing off `B_R`, and a factor that is bounded and Hölder on `B_R`; such products are
globally Hölder (`TauCeti.PDE.holderOnWith_sum_smul_fderiv_fderiv_cutoff_mul` with the whole space
as the set `t`). On the ball the lower-order factors `u` and `∂ⱼu`
are Lipschitz, with constant `N`, hence `α`-Hölder. This bounds the Hölder constant of `L w` by
`C (K + N)`, where `K` is the Hölder constant of `L u`, and `‖D²w‖_{L²} ≤ C N`; the Hessian of
`w` is supported in `B_R` and globally Hölder a priori. The compact-support estimate then bounds the
Hölder constant of `D²w`, which equals `D²u` near `closedBall x₀ ρ`.

## Main declaration

* `TauCeti.PDE.exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv`: the
  interior Schauder estimate on small balls.

## References

* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  Chapter 6, proof of Theorem 6.2 (localization of the Schauder estimate by cutoffs).
-/

public section

noncomputable section

open MeasureTheory Metric Set Filter Topology
open scoped NNReal ENNReal ContDiff

namespace TauCeti.PDE

variable {n : ℕ}

local notation "E" => EuclideanSpace ℝ (Fin (n + 1))

/-- The cutoff product `ζ u` of a cutoff `ζ` supported in the ball `B_R` and a `C²` function `u`
on `B_R` with bounds `N` on `u` and its first two derivatives and a Hölder Hessian is a `C²`
function with Hölder Hessian supported in `closedBall x₀ R`. The operator `∑ᵢⱼ aᵢⱼ ∂ᵢ∂ⱼ` applied
to it is globally Hölder with constant `Z K + N B₂`, and the `L²` norm of its Hessian is at most
`|closedBall 0 R|^{1/2} (n+1)² 4 Z N`. The constants `δ` and `B₂` are given by their definitions. -/
private theorem cutoff_mul_data {ζ u : E → ℝ} {x₀ : E} {R : ℝ} {α Z N K V L M δ B₂ : ℝ≥0}
    {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} (hα1 : α ≤ 1)
    (hζ2 : ContDiffOn ℝ 2 ζ (ball x₀ R)) (hζs : tsupport ζ ⊆ ball x₀ R)
    (hZ0 : HolderWith Z α ζ ∧ ∀ x, |ζ x| ≤ Z)
    (hZ1 : ∀ i, HolderWith Z α (fun x => fderiv ℝ ζ x (EuclideanSpace.single i 1)) ∧
      ∀ x, |fderiv ℝ ζ x (EuclideanSpace.single i 1)| ≤ Z)
    (hZ2 : ∀ i j, HolderWith Z α (fun x =>
        fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
      ∀ x, |fderiv ℝ (fderiv ℝ ζ) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)| ≤ Z)
    (hu : ContDiffOn ℝ 2 u (ball x₀ R)) (hN0 : ∀ x ∈ ball x₀ R, |u x| ≤ N)
    (hN1 : ∀ x ∈ ball x₀ R, ‖fderiv ℝ u x‖ ≤ N)
    (hN2 : ∀ x ∈ ball x₀ R, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N)
    (hV : HolderOnWith V α (iteratedFDeriv ℝ 2 u) (ball x₀ R))
    (hL : ∀ i j, HolderOnWith L α (fun x => a x i j) (closedBall x₀ R))
    (hM : ∀ x ∈ closedBall x₀ R, ∀ i j, |a x i j| ≤ M)
    (hK : HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
      (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (ball x₀ R))
    (hδ : δ = (2 * R).toNNReal ^ ((1 : ℝ) - α))
    (hB₂ : B₂ = (n + 1) ^ 2 * (M * Z + (3 * Z * L + M * (3 * (Z * δ + Z))))) :
    ContDiff ℝ 2 (ζ * u) ∧ MemHolder α (iteratedFDeriv ℝ 2 (ζ * u)) ∧
      HolderWith (Z * K + N * B₂) α (fun x => ∑ i, ∑ j, a x i j •
        fderiv ℝ (fderiv ℝ (ζ * u)) x (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) ∧
      Function.support (iteratedFDeriv ℝ 2 (ζ * u)) ⊆ closedBall x₀ R ∧
      (eLpNorm (iteratedFDeriv ℝ 2 (ζ * u)) 2 volume).toReal ≤
        (volume (closedBall (0 : E) R)).toReal ^ (2⁻¹ : ℝ) *
          (((n : ℝ) + 1) ^ 2 * (4 * Z)) * N := by
  subst hB₂ hδ
  have hsR : ball x₀ R ⊆ closedBall x₀ R := ball_subset_closedBall
  obtain ⟨hHu, hHdu⟩ := (convex_ball x₀ R).holderOnWith_and_holderOnWith_fderiv_apply_of_norm_le
    (D := (2 * R).toNNReal) hα1 (fun _ hx _ hy => edist_le_two_mul_of_mem_ball hx hy)
    isOpen_ball subset_rfl hu hN1 hN2
  obtain ⟨hdu, hd2u⟩ := abs_fderiv_apply_single_le_and_abs_fderiv_fderiv_apply_single_single_le
    (S := ball x₀ R ∩ univ) (fun x hx => hN1 x hx.1) fun x hx => hN2 x hx.1
  have hw : ContDiff ℝ 2 (ζ * u) := hu.contDiff_smul_of_tsupport_subset isOpen_ball hζ2 hζs
  have htU : univ ∩ tsupport ζ ⊆ ball x₀ R := fun x hx => hζs hx.2
  have hWH := holderOnWith_fderiv_fderiv_cutoff_mul isOpen_ball hζ2 hζs htU hZ0 hZ1 hZ2 hu
    (fun x hx => hN0 x hx.1) hdu hd2u (hHu.mono inter_subset_left)
    (fun i => (hHdu _ (by simp)).mono inter_subset_left) fun i j => by
      simpa [iteratedFDeriv_two_apply] using
        (hV.apply_orthonormalBasis (EuclideanSpace.basisFun _ ℝ) i j).mono
          (inter_subset_left (t := univ))
  have hsupp : Function.support (iteratedFDeriv ℝ 2 (ζ * u)) ⊆ closedBall x₀ R :=
    (support_iteratedFDeriv_subset 2).trans (tsupport_mul_subset_left.trans (hζs.trans hsR))
  refine ⟨hw, (holderOnWith_univ.1 (.of_apply_orthonormalBasis (EuclideanSpace.basisFun _ ℝ)
    fun i j => by simpa [iteratedFDeriv_two_apply] using (hWH i j).1)).memHolder,
    holderOnWith_univ.1 ((holderOnWith_sum_smul_fderiv_fderiv_cutoff_mul isOpen_ball hζ2 hζs htU
      hZ0 hZ1 hZ2 hu (fun x hx => hN0 x hx.1) hdu hd2u (hHu.mono inter_subset_left)
      (fun i => (hHdu _ (by simp)).mono inter_subset_left)
      (fun i j => (hL i j).mono (inter_subset_left.trans hsR))
      (fun x hx => hM x (hsR hx.1)) (hK.mono inter_subset_left)).mono_const (le_of_eq (by ring))),
    hsupp, ?_⟩
  exact (Measure.toReal_eLpNorm_iteratedFDeriv_two_le_of_support_subset_closedBall (p := 2) volume
    (EuclideanSpace.basisFun _ ℝ) (hw.continuous_iteratedFDeriv le_rfl) hsupp
    (B := 4 * Z * N) fun x i j => by simpa using (hWH i j).2 x (mem_univ x)).trans_eq
    (by simp only [Fintype.card_fin, ENNReal.toReal_ofNat]; push_cast; ring)

/-- **The interior Schauder estimate on small balls.** Let `0 < α < 1`. There is `C₀ > 0`,
depending only on dimension and `α`, with the following property. Let `0 < λ`, `Λ`, `L`, `M` and
`R` be given, put `κ = C₀ (Λ / λ)^(1 + (n+1)/4 + α/2)`, and assume the scale condition

`2 κ (n+1)² (1 + 2ᵅ) L Rᵅ ≤ λ`.

Then for every `ρ < R` there is `C`, depending only on `n`, `α`, `λ`, `Λ`, `L`, `M`, `R` and `ρ`,
with the following property. Let `a` be `α`-Hölder entrywise with constant `L` and bounded entrywise
by `M` on the closed ball `closedBall x₀ R`, and suppose `a x₀` has ellipticity bounds `λ, Λ`. Put
`L u = ∑ᵢⱼ aᵢⱼ ∂ᵢⱼu`. Let `u` be `C²` on the open ball `B_R`, with `|u|`, `‖Du‖` and `‖D²u‖` bounded
by `N` there and with `D²u` `α`-Hölder on `B_R` (with any constant). If `L u` is `α`-Hölder on `B_R`
with constant `K`, then `D²u` is `α`-Hölder on `closedBall x₀ ρ` with constant `C (K + N)`.

The constant `C` does not depend on the centre `x₀` or on the coefficient field `a` beyond the
bounds `λ`, `Λ`, `L` and `M`; this uniformity is what makes the estimate usable on infinitely many
balls at once. -/
theorem exists_holderOnWith_iteratedFDeriv_two_closedBall_of_sum_smul_fderiv_fderiv
    {α : ℝ≥0} (hα : 0 < α) (hα1 : α < 1) :
    ∃ C₀ : ℝ, 0 < C₀ ∧
      ∀ {lam Lam : ℝ} {L M : ℝ≥0} {R : ℝ}, 0 < lam →
      2 * (C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)) * ((n : ℝ) + 1) ^ 2 *
        ((1 + 2 ^ (α : ℝ)) * L * R ^ (α : ℝ)) ≤ lam →
      ∀ {ρ : ℝ}, ρ < R → ∃ C : ℝ≥0,
      ∀ {a : E → Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ} {x₀ : E},
      (∀ ξ : E, lam * ‖ξ‖ ^ 2 ≤ (a x₀).toQuadraticForm' ξ) →
      (∀ ξ : E, (a x₀).toQuadraticForm' ξ ≤ Lam * ‖ξ‖ ^ 2) →
      (∀ i j, HolderOnWith L α (fun x => a x i j) (closedBall x₀ R)) →
      (∀ x ∈ closedBall x₀ R, ∀ i j, |a x i j| ≤ M) →
      ∀ {u : E → ℝ} {N K V : ℝ≥0}, ContDiffOn ℝ 2 u (ball x₀ R) →
        (∀ x ∈ ball x₀ R, |u x| ≤ N) → (∀ x ∈ ball x₀ R, ‖fderiv ℝ u x‖ ≤ N) →
        (∀ x ∈ ball x₀ R, ‖iteratedFDeriv ℝ 2 u x‖ ≤ N) →
        HolderOnWith V α (iteratedFDeriv ℝ 2 u) (ball x₀ R) →
        HolderOnWith K α (fun x => ∑ i, ∑ j, a x i j • fderiv ℝ (fderiv ℝ u) x
          (EuclideanSpace.single i 1) (EuclideanSpace.single j 1)) (ball x₀ R) →
        HolderOnWith (C * (K + N)) α (iteratedFDeriv ℝ 2 u) (closedBall x₀ ρ) := by
  obtain ⟨C₀, hC₀, hCS⟩ :=
    exists_holderWith_iteratedFDeriv_two_of_support_subset_closedBall hα hα1 (n := n)
  refine ⟨C₀, hC₀, fun {lam Lam L M R} hlam hsmall {ρ} hρR => ?_⟩
  -- If `R ≤ 0` then `ρ < 0` and the closed ball is empty.
  rcases le_or_gt R 0 with hR | hR
  · exact ⟨0, fun {a x₀} _ _ _ _ {u N K V} _ _ _ _ _ _ => by
      rw [closedBall_eq_empty.2 (hρR.trans_le hR)]
      exact holderOnWith_empty _ _ _⟩
  -- Cutoffs about every centre with one constant `Z`.
  obtain ⟨Z, hZ⟩ := exists_forall_exists_cutoff (n := n) hα1.le hρR
  -- The constants of the estimate, which do not depend on `u`, `a` or `x₀`.
  set δ : ℝ≥0 := (2 * R).toNNReal ^ ((1 : ℝ) - α)
  set κ : ℝ := C₀ * (Lam / lam) ^ (1 + ((n : ℝ) + 1) / 4 + α / 2)
  set Q : ℝ := ((n : ℝ) + 1) ^ 2 * (L * 2 ^ (α : ℝ)) / lam *
      (volume (ball (0 : E) R) ^ (-((2 : ℝ)⁻¹))).toReal + R ^ (-(((n : ℝ) + 1) / 2 + α))
  set B₂ : ℝ≥0 := (n + 1) ^ 2 * (M * Z + (3 * Z * L + M * (3 * (Z * δ + Z))))
  set A₃ : ℝ := (volume (closedBall (0 : E) R)).toReal ^ (2⁻¹ : ℝ) * (((n : ℝ) + 1) ^ 2 * (4 * Z))
  refine ⟨(2 * κ * (Z / lam + B₂ / lam + Q * A₃)).toNNReal,
    fun {a x₀} hEll hEll' hL hM {u N K V} hu hN0 hN1 hN2 hV hK => ?_⟩
  -- The cutoff `ζ` about `x₀`.
  obtain ⟨ζ, hζ, hζ1, hζs, hZ0, hZ1, hZ2⟩ := hZ x₀
  have hζ2 : ContDiffOn ℝ 2 ζ (ball x₀ R) := (hζ.of_le (by norm_cast)).contDiffOn
  -- The cutoff product `w = ζ u`, with bounds on `u` and the `L²` norm of `D²w`.
  set w : E → ℝ := ζ * u
  obtain ⟨hw, hmem, hLw, hsupp, hL2⟩ := cutoff_mul_data hα1.le hζ2 hζs hZ0 hZ1 hZ2 hu hN0 hN1 hN2
    hV hL hM hK (δ := δ) (B₂ := B₂) rfl rfl
  have hsmall' : 2 * κ * ((n : ℝ) + 1) ^ 2 *
      (L * R ^ (α : ℝ) + (L * 2 ^ (α : ℝ)) * R ^ (α : ℝ)) ≤ lam := by
    convert hsmall using 2
    ring
  have key := hCS hlam hEll hEll' (L := L) (K := Z * K + N * B₂) (r := R) hR.le hR hsmall' hL hw
    hmem hsupp hLw
  -- Comparison of the constants.
  have hlamLam : lam ≤ Lam := by
    have h := (hEll (EuclideanSpace.single 0 1)).trans (hEll' (EuclideanSpace.single 0 1))
    simpa using h
  have hbound := two_mul_mul_add_div_add_mul_le (e := 1 + ((n : ℝ) + 1) / 4 + α / 2) (Z := Z)
    (B := B₂) (K := K) (N := N) hC₀.le hlam hlamLam (by positivity : 0 ≤ Q)
    (by positivity : 0 ≤ A₃) hL2
  -- On a neighbourhood of `closedBall x₀ ρ` the cutoff is one, so `D²w = D²u` there.
  have hwu (x : E) (hx : x ∈ closedBall x₀ ρ) :
      iteratedFDeriv ℝ 2 w x = iteratedFDeriv ℝ 2 u x :=
    Filter.EventuallyEq.iteratedFDeriv_mul_eq (by
      filter_upwards [mem_interior_iff_mem_nhds.1 (hζ1 hx)] with y hy
      simpa using hy)
  intro x hx y hy
  rw [← hwu x hx, ← hwu y hy]
  refine (key x y).trans ?_
  gcongr
  exact Real.toNNReal_le_iff_le_coe.2 hbound

end TauCeti.PDE
