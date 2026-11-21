/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Dagger.DaggerAlgebra
public import TauCeti.RingTheory.Dagger.OptionSeries
public import TauCeti.RingTheory.Affinoid.SupSeminorm

import Mathlib.Algebra.Polynomial.Lifts
import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Dagger.FaithfullyFlat
import TauCeti.RingTheory.Dagger.Subst
import TauCeti.RingTheory.Dagger.SupSeminorm
import TauCeti.RingTheory.Dagger.Weierstrass
import TauCeti.Topology.Algebra.Ring.MaximalIdeals

/-!
# Weak completeness of dagger algebras

Let `K` be a complete nontrivially normed ultrametric field and `A` a `K`-dagger algebra. This
file proves that `A` is *weakly complete*: for elements `x₁, …, xₙ ∈ A` with supremum seminorm
`|xᵢ|sup ≤ 1`, the evaluation `K[X₁, …, Xₙ] → A`, `Xᵢ ↦ xᵢ`, extends to a `K`-algebra
homomorphism `K⟨X₁, …, Xₙ⟩† → A` from the Monsky–Washnitzer algebra. This is what makes
overconvergent series in elements of a dagger algebra meaningful, and it is the input for the
universal properties of dagger tensor products and rational localisations.

The extension is built from integral equations. For a presentation `π : W ↠ A` of `A` by a
Monsky–Washnitzer algebra `W`, the elements of supremum seminorm at most one are exactly the
elements integral over `π(W°)`, the image of the Gauss unit ball. Given such an equation
`ω(x) = 0`, with `ω` monic over `W°`, the polynomial `ω` is distinguished at the unit radius, so
overconvergent Weierstrass division identifies `W[Y] ⧸ (ω)` with `W⟨Y⟩† ⧸ (ω)`, and evaluation at
`x` extends `π` to `W⟨Y⟩† → A` with `Y ↦ x`. Adjoining the `xᵢ` one at a time gives the
homomorphism.

The integral equations come from the affinoid algebra `T ⧸ I T`, where `T` is the Tate algebra and
`I = ker π`. The residue of a lift of `x` there has supremum seminorm at most one, so it is
integral over the image of the Gauss unit ball of `T`
(`AlgHom.isIntegral_map_unitClosedBall_iff_supSeminorm_le_one`). Approximating the coefficients
of that equation, and its defect in `I T`, by overconvergent series moves the equation into `W`,
at the cost of an error of Gauss norm at most one, which is absorbed into the constant
coefficient.

## Main results

* `TauCeti.Dagger.washnitzerAlgebra.exists_algHom_option_of_isIntegral`: a homomorphism
  `W →ₐ[K] A` extends to `W⟨Y⟩† →ₐ[K] A` sending `Y` to any element integral over the image of
  the Gauss unit ball.
* `TauCeti.Dagger.washnitzerAlgebra.isIntegral_map_unitClosedBall_iff_supSeminorm_le_one`: for
  a presentation `π : W ↠ A`, an element is integral over `π(W°)` if and only if its supremum
  seminorm is at most one.
* `TauCeti.Dagger.IsDaggerAlgebra.exists_algHom_washnitzerAlgebra`: **weak completeness**, every
  family of elements of supremum seminorm at most one is the image of the variables under a
  `K`-algebra homomorphism from the Monsky–Washnitzer algebra.

## References

* E. Grosse-Klönne, *Rigid analytic spaces with overconvergent structure sheaf*,
  J. reine angew. Math. 519 (2000), §1, 1.9.
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §6.1.1 and
  §6.2.2 (the same statements for Tate and affinoid algebras).
-/

public section

namespace TauCeti.Dagger

open _root_.MvPowerSeries Polynomial

namespace washnitzerAlgebra

section Adjoin

variable {K : Type*} [NormedField K] [IsUltrametricDist K] [CompleteSpace K] {σ : Type*}
  {A : Type*} [CommRing A] [Algebra K A]

local notation "T " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- **Adjoining an integral element.** A `K`-algebra homomorphism `φ : K⟨X⟩† → A` extends to
`K⟨X, Y⟩† → A`, sending `Y` to `x`, as soon as `x` is integral over the image under `φ` of the
Gauss unit ball. -/
theorem exists_algHom_option_of_isIntegral (φ : washnitzerAlgebra σ K →ₐ[K] A) {x : A}
    (hx : IsIntegral ((Subring.unitClosedBall (washnitzerAlgebra σ K)).map φ.toRingHom) x) :
    ∃ ψ : washnitzerAlgebra (Option σ) K →ₐ[K] A,
      (∀ f, ψ (optionC f) = φ f) ∧ ψ (X (Option σ) K none) = x := by
  classical
  set B := Subring.unitClosedBall (washnitzerAlgebra σ K)
  set R := B.map φ.toRingHom
  obtain ⟨p, hpm, hp⟩ := hx
  -- Lift the equation to a monic polynomial `ω` over `W` with coefficients in the unit ball.
  let ι : B →+* R := φ.toRingHom.restrict B R fun a ha ↦ Subring.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨q, hqp, -, hqm⟩ := lifts_and_natDegree_eq_and_monic (f := ι)
    ((lifts_iff_coeff_lifts p).mpr fun k ↦ by
      obtain ⟨a, ha, hak⟩ := Subring.mem_map.mp (p.coeff k).2
      exact ⟨⟨a, ha⟩, Subtype.ext hak⟩) hpm
  set ω := q.map B.subtype
  have hωm : ω.IsMonicOfDegree ω.natDegree := ⟨rfl, hqm.map _⟩
  have hω : PowerSeries.IsDistinguished 1 ω.natDegree
      (ω.map (toTate σ K).toRingHom : PowerSeries (T σ)) :=
    PowerSeries.isDistinguished_of_isMonicOfDegree one_pos
      ⟨by rw [hωm.monic.natDegree_map], hωm.monic.map _⟩ fun k _ ↦ by
        simpa [ω, Polynomial.coeff_map, norm_toTate] using
          Subring.mem_unitClosedBall.mp (q.coeff k).2
  -- Evaluate at `x` on `W[Y] ⧸ (ω) ≅ W⟨Y⟩† ⧸ (ω)`.
  have hev : ω.eval₂ (φ : washnitzerAlgebra σ K →+* A) x = 0 := by
    have hcomp : (φ : washnitzerAlgebra σ K →+* A).comp B.subtype = (algebraMap R A).comp ι :=
      RingHom.ext fun _ ↦ rfl
    rw [eval₂_map, hcomp, ← eval₂_map, hqp]
    exact hp
  let e := polynomialQuotientEquiv hω hωm
  let ψ : washnitzerAlgebra (Option σ) K →ₐ[K] A :=
    (AdjoinRoot.liftAlgHom ω φ x hev).comp (e.symm.toAlgHom.comp (Ideal.Quotient.mkₐ K _))
  have hψ (r : Polynomial (washnitzerAlgebra σ K)) :
      ψ (polynomialToOption r) = AdjoinRoot.liftAlgHom ω φ x hev (AdjoinRoot.mk ω r) := by
    simp only [ψ, AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, AlgEquiv.coe_toAlgHom]
    rw [← polynomialQuotientEquiv_mk hω hωm, AlgEquiv.symm_apply_apply]
  refine ⟨ψ, fun f ↦ ?_, ?_⟩
  · rw [← polynomialToOption_C, hψ, AdjoinRoot.mk_C, AdjoinRoot.liftAlgHom_of]
  · rw [← polynomialToOption_X, hψ, AdjoinRoot.mk_X, AdjoinRoot.liftAlgHom_root]

end Adjoin

section Integral

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {σ : Type*} [Finite σ] {A : Type*} [CommRing A] [Algebra K A]

local notation "T " σ:max => IsRestricted.subring (R := K) (fun _ : σ ↦ (1 : ℝ))

/-- For a presentation `π : W ↠ A`, the supremum seminorm of the residue of a series in
`T ⧸ (ker π) T` is at most that of its image in `A`: every classical point of `T ⧸ (ker π) T` lies
over a classical point of `A` with the same residue field. -/
private theorem supSeminorm_mk_map_toTate_le {π : washnitzerAlgebra σ K →ₐ[K] A}
    (hπ : Function.Surjective π) (f : washnitzerAlgebra σ K) :
    supSeminorm K (Ideal.Quotient.mk ((RingHom.ker π).map (toTate σ K)) (toTate σ K f)) ≤
      supSeminorm K (π f) := by
  have := IsDaggerAlgebra.of_surjective_washnitzerAlgebra π hπ
  set J := (RingHom.ker π).map (toTate σ K)
  have hB : IsAffinoidAlgebra K (T σ ⧸ J) := isAffinoidAlgebra_tate.quotient J
  let ψ : washnitzerAlgebra σ K →ₐ[K] T σ ⧸ J := (Ideal.Quotient.mkₐ K J).comp (toTate σ K)
  refine supSeminorm_le (supSeminorm_nonneg _) fun z ↦ ?_
  -- The pullback `m` of `z` to `W` contains `ker π`, so it is the pullback of a point of `A`.
  have hm : (z.asIdeal.comap ψ).IsMaximal := hB.comap_isMaximal ψ z.asIdeal
  have hker : RingHom.ker π ≤ z.asIdeal.comap ψ := fun a ha ↦ by
    have hψa : ψ a = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem _ ha)
    rw [Ideal.mem_comap, hψa]
    exact z.asIdeal.zero_mem
  have hcomap : ((z.asIdeal.comap ψ).map π).comap π = z.asIdeal.comap ψ := by
    rw [Ideal.comap_map_of_surjective' π hπ, sup_eq_left.mpr hker]
  have hy : ((z.asIdeal.comap ψ).map π).IsMaximal := by
    refine (Ideal.map_eq_top_or_isMaximal_of_surjective π hπ hm).resolve_left fun h ↦
      hm.ne_top ?_
    rw [← hcomap, h, Ideal.comap_top]
  have hx : (((z.asIdeal.comap ψ).map π).comap π).IsMaximal := by
    rw [hcomap]
    exact hm
  have hpt : (⟨_, hx⟩ : MaximalSpectrum (washnitzerAlgebra σ K)) = ⟨_, hm⟩ :=
    MaximalSpectrum.ext hcomap
  calc pointNorm K z (Ideal.Quotient.mk J (toTate σ K f))
      = pointNorm K ⟨_, hm⟩ f := (pointNorm_comap ψ z hm f).symm
    _ = pointNorm K ⟨_, hy⟩ (π f) := by rw [← hpt, pointNorm_comap π ⟨_, hy⟩ hx]
    _ ≤ supSeminorm K (π f) := IsDaggerAlgebra.pointNorm_le_supSeminorm _ _

/-- A lift `y ∈ W` of an element of supremum seminorm at most one satisfies, in the Tate algebra
`T`, a monic equation with coefficients of Gauss norm at most one modulo `(ker π) T`. -/
private theorem exists_monic_aeval_mem_map_toTate {π : washnitzerAlgebra σ K →ₐ[K] A}
    (hπ : Function.Surjective π) {y : washnitzerAlgebra σ K} (hy : supSeminorm K (π y) ≤ 1) :
    ∃ P : (T σ)[X], P.Monic ∧ (∀ i, ‖P.coeff i‖ ≤ 1) ∧
      aeval (toTate σ K y) P ∈ (RingHom.ker π).map (toTate σ K) := by
  set J := (RingHom.ker π).map (toTate σ K)
  set B := Subring.unitClosedBall (T σ)
  let q := Ideal.Quotient.mkₐ K J
  obtain ⟨Q, hQm, hQ⟩ := (q.isIntegral_map_unitClosedBall_iff_supSeminorm_le_one
    (Ideal.Quotient.mkₐ_surjective K J)).mpr ((supSeminorm_mk_map_toTate_le hπ y).trans hy)
  -- Lift the equation over `q(T°)` to a monic polynomial over `T°`.
  let ι : B →+* B.map q.toRingHom :=
    q.toRingHom.restrict B _ fun a ha ↦ Subring.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨P, hPQ, -, hPm⟩ := lifts_and_natDegree_eq_and_monic (f := ι)
    ((lifts_iff_coeff_lifts Q).mpr fun k ↦ by
      obtain ⟨a, ha, hak⟩ := Subring.mem_map.mp (Q.coeff k).2
      exact ⟨⟨a, ha⟩, Subtype.ext hak⟩) hQm
  refine ⟨P.map B.subtype, hPm.map _, fun i ↦ ?_, ?_⟩
  · rw [Polynomial.coeff_map]
    exact Subring.mem_unitClosedBall.mp (P.coeff i).2
  · have hcomp : (algebraMap (B.map q.toRingHom) (T σ ⧸ J)).comp ι =
        (algebraMap (T σ) (T σ ⧸ J)).comp B.subtype :=
      RingHom.ext fun _ ↦ rfl
    rw [← Ideal.Quotient.eq_zero_iff_mem, ← Ideal.Quotient.mkₐ_eq_mk (T σ), ← aeval_algHom_apply,
      Ideal.Quotient.mkₐ_eq_mk, aeval_def, eval₂_map, ← hcomp, ← eval₂_map, hPQ]
    exact hQ

omit [CompleteSpace K] [Finite σ] in
/-- **Moving a monic equation from `T` to `W`.** If `y ∈ W` satisfies, modulo `I T`, a monic
equation over the Gauss unit ball of `T`, then modulo `I` it satisfies a monic equation over the
Gauss unit ball of `W` of the same degree, up to a constant term `e` of Gauss norm at most one. -/
private theorem exists_sum_sub_mem_of_aeval_mem_map_toTate (I : Ideal (washnitzerAlgebra σ K))
    {y : washnitzerAlgebra σ K} {P : (T σ)[X]} (hPm : P.Monic) (hP1 : ∀ i, ‖P.coeff i‖ ≤ 1)
    (hPI : aeval (toTate σ K y) P ∈ I.map (toTate σ K)) :
    ∃ (p : Fin P.natDegree → washnitzerAlgebra σ K) (e : washnitzerAlgebra σ K),
      (∀ i, ‖p i‖ ≤ 1) ∧ ‖e‖ ≤ 1 ∧
        y ^ P.natDegree + ∑ i, p i * y ^ (i : ℕ) - e ∈ I := by
  set r := P.natDegree
  set t := toTate σ K y
  -- Approximate the coefficients of `P` to within `M⁻ʳ`, where `M` bounds `‖t‖` and `1`, and the
  -- value `P(t) ∈ I T` to within `1` by the image of an element `g ∈ I`.
  set M : ℝ := max 1 ‖y‖
  have hM : 1 ≤ M := le_max_left _ _
  have hε : 0 < (M ^ r)⁻¹ := inv_pos.mpr (pow_pos (one_pos.trans_le hM) r)
  choose p hp using fun i : Fin r ↦
    Metric.denseRange_iff.mp denseRange_toTate (P.coeff i) _ hε
  obtain ⟨_, ⟨g, hg, rfl⟩, hgdist⟩ := Metric.mem_closure_iff.mp
    (Ideal.map_subset_closure_image_of_denseRange denseRange_toTate I hPI) 1 one_pos
  -- The defect `e` of the approximate equation has Gauss norm at most one.
  set e : washnitzerAlgebra σ K := y ^ r + ∑ i : Fin r, p i * y ^ (i : ℕ) - g
  have hPt : aeval t P = t ^ r + ∑ i : Fin r, P.coeff i * t ^ (i : ℕ) := by
    rw [Fin.sum_univ_eq_sum_range (fun i ↦ P.coeff i * t ^ i) r]
    conv_lhs => rw [hPm.as_sum]
    simp [eval_finsetSum, r]
  have hdecomp : toTate σ K e = (aeval t P - toTate σ K g) +
      ∑ i : Fin r, (toTate σ K (p i) - P.coeff i) * t ^ (i : ℕ) := by
    simp only [e, t, hPt, map_sub, map_add, map_sum, map_mul, map_pow, sub_mul,
      Finset.sum_sub_distrib]
    ring
  have hterm (i : Fin r) : ‖(toTate σ K (p i) - P.coeff i) * t ^ (i : ℕ)‖ ≤ 1 := by
    have hd : ‖toTate σ K (p i) - P.coeff i‖ ≤ (M ^ r)⁻¹ := by
      rw [← dist_eq_norm, dist_comm]
      exact (hp i).le
    have ht : ‖t ^ (i : ℕ)‖ ≤ M ^ r :=
      (norm_pow_le _ _).trans ((pow_le_pow_left₀ (norm_nonneg _)
        ((norm_toTate y).trans_le (le_max_right _ _)) _).trans
          (pow_le_pow_right₀ hM i.2.le))
    calc _ ≤ ‖toTate σ K (p i) - P.coeff i‖ * ‖t ^ (i : ℕ)‖ := norm_mul_le _ _
      _ ≤ (M ^ r)⁻¹ * M ^ r := mul_le_mul hd ht (norm_nonneg _) hε.le
      _ = 1 := inv_mul_cancel₀ (pow_pos (one_pos.trans_le hM) r).ne'
  refine ⟨p, e, fun i ↦ ?_, ?_, by simpa [e] using hg⟩
  · rw [← norm_toTate, ← add_sub_cancel (P.coeff i) (toTate σ K (p i))]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hP1 i) ?_)
    rw [← dist_eq_norm, dist_comm]
    exact (hp i).le.trans (inv_le_one_of_one_le₀ (one_le_pow₀ hM))
  · rw [← norm_toTate, hdecomp]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [← dist_eq_norm]
      exact hgdist.le
    · exact IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
        fun i _ ↦ hterm i

/-- The direction `|x|sup ≤ 1 → x` integral of
`TauCeti.Dagger.washnitzerAlgebra.isIntegral_map_unitClosedBall_iff_supSeminorm_le_one`. -/
private theorem isIntegral_map_unitClosedBall_of_supSeminorm_le_one
    {π : washnitzerAlgebra σ K →ₐ[K] A} (hπ : Function.Surjective π) {x : A}
    (hx : supSeminorm K x ≤ 1) :
    IsIntegral ((Subring.unitClosedBall (washnitzerAlgebra σ K)).map π.toRingHom) x := by
  obtain ⟨y, rfl⟩ := hπ x
  obtain ⟨P, hPm, hP1, hPI⟩ := exists_monic_aeval_mem_map_toTate hπ hx
  set r := P.natDegree
  rcases Nat.eq_zero_or_pos r with hr | hr
  · -- A monic equation of degree zero puts `1` in `(ker π) T`, so `ker π = ⊤` and `A = 0`.
    have h1 : (1 : washnitzerAlgebra σ K) ∈ RingHom.ker π := by
      rw [← Ideal.comap_map_toTate (RingHom.ker π), Ideal.mem_comap, map_one]
      simpa [hPm.natDegree_eq_zero.mp hr] using hPI
    have : Subsingleton A := subsingleton_of_zero_eq_one (by simpa using h1.symm)
    exact Subsingleton.elim (π y) 0 ▸ isIntegral_zero
  obtain ⟨p, e, hp1, he, hI⟩ := exists_sum_sub_mem_of_aeval_mem_map_toTate _ hPm hP1 hPI
  -- The image of the equation of `y` is a monic equation of `π y` over `π(W°)`.
  set R := (Subring.unitClosedBall (washnitzerAlgebra σ K)).map π.toRingHom
  have hmem {a : washnitzerAlgebra σ K} (ha : ‖a‖ ≤ 1) : π a ∈ R :=
    Subring.mem_map.mpr ⟨a, Subring.mem_unitClosedBall.mpr ha, rfl⟩
  refine ⟨Polynomial.X ^ r + (∑ i : Fin r, Polynomial.C (⟨π (p i), hmem (hp1 i)⟩ : R) *
    Polynomial.X ^ (i : ℕ) - Polynomial.C (⟨π e, hmem he⟩ : R)),
    monic_X_pow_add <| (degree_sub_le _ _).trans_lt <|
      max_lt (degree_sum_fin_lt _) (degree_C_le.trans_lt (by exact_mod_cast hr)), ?_⟩
  have h : π (y ^ r + ∑ i, p i * y ^ (i : ℕ) - e) = 0 := hI
  simp only [map_sub, map_add, map_sum, map_mul, map_pow] at h
  have halg (a : R) : algebraMap R A a = a := (rfl)
  simpa [eval₂_finsetSum, halg, add_sub_assoc] using h

/-- **Elements of supremum seminorm at most one are the integral elements over a presentation
ring.** For a presentation `π : K⟨X⟩† ↠ A` of a dagger algebra, an element is integral over the
image under `π` of the Gauss unit ball if and only if its supremum seminorm is at most one. -/
theorem isIntegral_map_unitClosedBall_iff_supSeminorm_le_one {π : washnitzerAlgebra σ K →ₐ[K] A}
    (hπ : Function.Surjective π) {x : A} :
    IsIntegral ((Subring.unitClosedBall (washnitzerAlgebra σ K)).map π.toRingHom) x ↔
      supSeminorm K x ≤ 1 := by
  refine ⟨fun hx ↦ ?_, isIntegral_map_unitClosedBall_of_supSeminorm_le_one hπ⟩
  -- `x` is the image of a variable under a surjection `K⟨X, Y⟩† ↠ A` extending `π`.
  obtain ⟨ψ, hψ, rfl⟩ := exists_algHom_option_of_isIntegral π hx
  have hψs : Function.Surjective ψ := fun a ↦
    let ⟨f, hf⟩ := hπ a
    ⟨optionC f, (hψ f).trans hf⟩
  exact (supSeminorm_map_le_norm hψs _).trans (norm_X _).le

end Integral

end washnitzerAlgebra

namespace IsDaggerAlgebra

open Dagger.washnitzerAlgebra

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type*} [CommRing A] [Algebra K A]

/-- The statement of `exists_algHom_washnitzerAlgebra`, relative to a homomorphism `φ` from
`K⟨X_υ⟩†`, for the elements `x` indexed by `τ`: if every `x i` is integral over the image under
`φ` of the Gauss unit ball, then `φ` extends to `K⟨X_υ, X_τ⟩† → A` sending `X_τ` to `x`. -/
private abbrev ExtendsAlong (K : Type*) [NontriviallyNormedField K] [IsUltrametricDist K]
    (A : Type*) [CommRing A] [Algebra K A] (υ : Type*) (τ : Type*) : Prop :=
  ∀ (φ : Dagger.washnitzerAlgebra υ K →ₐ[K] A) (x : τ → A),
    (∀ i, IsIntegral
      ((Subring.unitClosedBall (Dagger.washnitzerAlgebra υ K)).map φ.toRingHom) (x i)) →
      ∃ ψ : Dagger.washnitzerAlgebra (υ ⊕ τ) K →ₐ[K] A,
        (∀ j, ψ (X _ K (Sum.inl j)) = φ (X υ K j)) ∧ ∀ i, ψ (X _ K (Sum.inr i)) = x i

/-- Adjoining finitely many integral elements one at a time. -/
private theorem extendsAlong {τ : Type*} [Finite τ] :
    ∀ υ : Type*, ExtendsAlong K A υ τ := by
  refine Finite.induction_empty_option (P := fun τ ↦ ∀ υ : Type _, ExtendsAlong K A υ τ)
    ?_ ?_ ?_ τ
  · -- Transport along an equivalence of the new variables.
    intro τ τ' e h υ φ x hx
    obtain ⟨ψ, hl, hr⟩ := h υ φ (x ∘ e) fun i ↦ hx (e i)
    refine ⟨ψ.comp (renameAlgEquiv (Equiv.sumCongr (Equiv.refl υ) e.symm)).toAlgHom,
      fun j ↦ ?_, fun i ↦ ?_⟩
    · simpa using hl j
    · simpa using hr (e.symm i)
  · -- No new variables.
    intro υ φ x _
    exact ⟨φ.comp (renameAlgEquiv (Equiv.sumEmpty υ PEmpty)).toAlgHom, fun j ↦ by simp,
      fun i ↦ i.elim⟩
  · -- Adjoin the element indexed by `none`, then the others by induction.
    intro τ _ ih υ φ x hx
    obtain ⟨φ', hφ', hnone⟩ := exists_algHom_option_of_isIntegral φ (hx none)
    have hle : (Subring.unitClosedBall (Dagger.washnitzerAlgebra υ K)).map φ.toRingHom ≤
        (Subring.unitClosedBall (Dagger.washnitzerAlgebra (Option υ) K)).map φ'.toRingHom := by
      rintro _ ⟨w, hw, rfl⟩
      exact ⟨optionC w, by simpa [Subring.mem_unitClosedBall] using hw, hφ' w⟩
    obtain ⟨ψ, hl, hr⟩ := ih (Option υ) φ' (x ∘ some) fun i ↦
      (hx (some i)).map_of_comp_eq (Subring.inclusion hle) (RingHom.id A) rfl
    let e : υ ⊕ Option τ ≃ Option υ ⊕ τ :=
      { toFun := Sum.elim (fun j ↦ Sum.inl (some j)) (Option.elim' (Sum.inl none) Sum.inr)
        invFun := Sum.elim (Option.elim' (Sum.inr none) Sum.inl) (fun i ↦ Sum.inr (some i))
        left_inv := by rintro (j | _ | i) <;> rfl
        right_inv := by rintro ((_ | j) | i) <;> rfl }
    refine ⟨ψ.comp (renameAlgEquiv e).toAlgHom, fun j ↦ ?_, ?_⟩
    · have h := hl (some j)
      rw [← optionC_X, hφ'] at h
      simpa [e] using h
    · rintro (_ | i)
      · simpa [e, hnone] using hl none
      · simpa [e] using hr i

/-- **Weak completeness of dagger algebras.** For finitely many elements `xᵢ` of a dagger algebra
`A` with supremum seminorm `|xᵢ|sup ≤ 1`, there is a `K`-algebra homomorphism
`K⟨X⟩† → A` from the Monsky–Washnitzer algebra sending each variable `Xᵢ` to `xᵢ`. It extends the
evaluation `K[X] → A` at the `xᵢ`. -/
theorem exists_algHom_washnitzerAlgebra [IsDaggerAlgebra K A] {τ : Type*} [Finite τ]
    (x : τ → A) (hx : ∀ i, supSeminorm K (x i) ≤ 1) :
    ∃ φ : Dagger.washnitzerAlgebra τ K →ₐ[K] A, ∀ i, φ (X τ K i) = x i := by
  obtain ⟨n, π, hπ⟩ := exists_surjective (K := K) (A := A)
  obtain ⟨ψ, -, hψ⟩ := extendsAlong (Fin n) π x fun i ↦
    (isIntegral_map_unitClosedBall_iff_supSeminorm_le_one hπ).mpr (hx i)
  -- Restrict to the variables indexed by `τ`.
  have h₀ (i : τ) : (MvPolynomial.X (R := K) (Sum.inr i : Fin n ⊕ τ)).constantCoeff = 0 := by
    simp
  have h₁ (i : τ) (m) : ‖(MvPolynomial.X (R := K) (Sum.inr i : Fin n ⊕ τ)).coeff m‖ ≤ 1 := by
    classical
    rw [MvPolynomial.coeff_X]
    split_ifs <;> simp
  exact ⟨ψ.comp (subst _ h₀ h₁), fun i ↦ by simp [hψ]⟩

end IsDaggerAlgebra

end TauCeti.Dagger
