/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Rigid.Affinoid.SupSeminorm
public import TauCeti.RingTheory.Affinoid.Restricted
public import TauCeti.RingTheory.Affinoid.SupSeminorm

import TauCeti.RingTheory.Affinoid.ContractiveRenorming
import TauCeti.RingTheory.Affinoid.MaximumModulus
import TauCeti.RingTheory.Affinoid.PowerBounded
import TauCeti.RingTheory.Affinoid.QuotientNorm
import TauCeti.RingTheory.Affinoid.ValueGroup

/-!
# Relatively compact affinoid subdomains

Let `φ : A → B` be a homomorphism of affinoid algebras over a complete nonarchimedean field `K`,
so that `Sp B` lies over `Sp A`, and let `U ⊆ Sp B` be an affinoid subdomain. Following Kiehl,
`U` is *relatively compact in `Sp B` over `A`*, or *inner*, written `U ⋐_A Sp B`, if there is a
surjection of `A`-algebras `ψ : A⟨X₁, …, Xₙ⟩ → B` such that every generator `ψ Xᵢ` has supremum
norm less than one on `U`. Geometrically, `ψ` is a closed immersion of `Sp B` into the relative
unit polydisc over `Sp A`, and `U` lands in a strictly smaller polydisc. Kiehl's proper mapping
theorem is formulated through finite covers by pairs of affinoids, one inner in the other.

The supremum norm on `U` is the supremum seminorm of the algebra of sections over `U`. By the
maximum modulus principle it is less than one exactly when the generators have absolute value
less than one at every classical point of `U`; by the value-group theorem a single radius
`ε < 1` in the divisible hull `√|Kˣ|` of the value group then bounds all generators on `U`. This
gives the polydisc form of the definition: `Sp B → Sp A⟨X⟩` maps `U` into the relative polydisc
of radius `ε`.

A finite homomorphism makes the whole of `Sp B` inner over `A`: scaled module generators,
of supremum norm less than one, already generate `B` as an `A`-algebra. In the other direction,
if `Sp B` is inner over `K` itself, every element `f` with `|f|sup ≤ 1` satisfies a monic
equation with coefficients in the unit ball of `K` modulo elements of supremum norm less than
one, so the canonical reduction of `B` is integral over the residue field. For the Tate
algebra `K⟨X₁, …, Xₙ⟩` with `n ≥ 1` the variable `X₁` admits no such equation, since a monic
polynomial in `X₁` over the unit ball has Gauss norm one: the closed unit polydisc is not inner
in itself over `K`.

## Main definitions

* `TauCeti.AffinoidSubdomain.IsInner`: `U ⋐_A Sp B`, relative compactness of an affinoid
  subdomain `U` of `Sp B` over `A`.

## Main results

* `TauCeti.AffinoidSubdomain.isInner_def`: the defining characterisation by supremum norms.
* `TauCeti.AffinoidSubdomain.isInner_iff_forall_pointNorm_lt`: the pointwise form of the
  definition.
* `TauCeti.AffinoidSubdomain.isInner_iff_exists_pointNorm_le`: a single bound `ε < 1` in the
  divisible hull of the value group suffices.
* `TauCeti.AffinoidSubdomain.isInner_iff_exists_mapsTo`: the relative-polydisc criterion.
* `TauCeti.AffinoidSubdomain.IsInner.anti`: a smaller affinoid subdomain is again inner.
* `TauCeti.AffinoidSubdomain.isInner_empty`: the empty subdomain is inner over every affinoid
  base.
* `TauCeti.AffinoidSubdomain.isInner_univ_of_finite`: for a finite homomorphism `φ`, the whole
  of `Sp B` is inner over `A`.
* `TauCeti.AffinoidSubdomain.IsInner.exists_monic_supSeminorm_aeval_lt_one`: if `Sp B` is inner
  over `K`, each `f` with `|f|sup ≤ 1` is a root of a monic polynomial over the unit ball of `K`
  up to an element of supremum norm less than one.
* `TauCeti.AffinoidSubdomain.not_isInner_univ_tate`: the closed unit polydisc of positive
  dimension is not inner in itself over `K`.

## References

* R. Kiehl, *Der Endlichkeitssatz für eigentliche Abbildungen in der nichtarchimedischen
  Funktionentheorie*, Invent. Math. 2 (1967), 191–214, §2.
* S. Bosch, *Lectures on Formal and Rigid Geometry*, Lecture Notes in Mathematics 2105,
  Springer, 2014, §6.3.
* [Bosch, Güntzer, Remmert, *Non-Archimedean Analysis*][bosch-guntzer-remmert], §9.6.2.
-/

public section

namespace TauCeti

open _root_.MvPowerSeries TauCeti.MvPowerSeries Polynomial

universe u

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidSubdomain

section Inner

variable {A : Type*} [NormedCommRing A] [NormedAlgebra K A] [IsUltrametricDist A]
  {B : Type u} [CommRing B] [Algebra K B]

/-- **Relative compactness of an affinoid subdomain** (Kiehl's *inner* subdomains),
`U ⋐_A Sp B`. Let `φ : A → B` be a `K`-algebra map from an algebra `A` with an ultrametric algebra
norm, so that the restricted series `A⟨X₁, …, Xₙ⟩` are defined; in applications `A` is affinoid
with a complete norm. An affinoid subdomain `U` of `Sp B` is inner over `A` if some surjection
`ψ : A⟨X₁, …, Xₙ⟩ → B` extending `φ` sends every variable `Xᵢ` to a function whose supremum norm
on `U` is less than one. -/
def IsInner (U : AffinoidSubdomain K B) (φ : A →ₐ[K] B) : Prop :=
  ∃ (n : ℕ) (ψ : IsRestricted.subring (R := A) (fun _ : Fin n ↦ 1) →ₐ[K] B),
    Function.Surjective ψ ∧ (∀ a, ψ (algebraMap A _ a) = φ a) ∧
      ∀ i, supSeminorm K (U.toSections (ψ ⟨X i, isRestricted_X _ i⟩)) < 1

variable {U : AffinoidSubdomain K B} {φ : A →ₐ[K] B}

/-- The defining property of `U ⋐_A Sp B`: some surjection `ψ : A⟨X₁, …, Xₙ⟩ → B` extending `φ`
sends every variable `Xᵢ` to a function of supremum norm less than one on `U`. -/
theorem isInner_def :
    U.IsInner φ ↔ ∃ (n : ℕ) (ψ : IsRestricted.subring (R := A) (fun _ : Fin n ↦ 1) →ₐ[K] B),
      Function.Surjective ψ ∧ (∀ a, ψ (algebraMap A _ a) = φ a) ∧
        ∀ i, supSeminorm K (U.toSections (ψ ⟨X i, isRestricted_X _ i⟩)) < 1 :=
  Iff.rfl

/-- **Pointwise form of relative compactness.** `U ⋐_A Sp B` exactly when some surjection
`ψ : A⟨X₁, …, Xₙ⟩ → B` extending `φ` satisfies `|(ψ Xᵢ)(y)| < 1` at every classical point `y`
of `U`. -/
theorem isInner_iff_forall_pointNorm_lt (hB : IsAffinoidAlgebra K B) :
    U.IsInner φ ↔ ∃ (n : ℕ) (ψ : IsRestricted.subring (R := A) (fun _ : Fin n ↦ 1) →ₐ[K] B),
      Function.Surjective ψ ∧ (∀ a, ψ (algebraMap A _ a) = φ a) ∧
        ∀ i, ∀ y ∈ U, pointNorm K y (ψ ⟨X i, isRestricted_X _ i⟩) < 1 := by
  simp only [isInner_def, supSeminorm_toSections_lt_iff hB U _ one_pos]

/-- **A single radius bounds the generators.** `U ⋐_A Sp B` exactly when some surjection
`ψ : A⟨X₁, …, Xₙ⟩ → B` extending `φ` and some `ε` with `0 < ε < 1` in the divisible hull
`√|Kˣ|` of the value group satisfy `|(ψ Xᵢ)(y)| ≤ ε` at every classical point `y` of `U`. -/
theorem isInner_iff_exists_pointNorm_le (hB : IsAffinoidAlgebra K B) :
    U.IsInner φ ↔ ∃ (n : ℕ) (ψ : IsRestricted.subring (R := A) (fun _ : Fin n ↦ 1) →ₐ[K] B),
      Function.Surjective ψ ∧ (∀ a, ψ (algebraMap A _ a) = φ a) ∧
        ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (∃ m : ℕ, 0 < m ∧ ∃ c : Kˣ, ε ^ m = ‖(c : K)‖) ∧
          ∀ i, ∀ y ∈ U, pointNorm K y (ψ ⟨X i, isRestricted_X _ i⟩) ≤ ε := by
  refine ⟨fun ⟨n, ψ, hψ, hφ, hX⟩ ↦ ?_, fun ⟨n, ψ, hψ, hφ, ε, _, hε1, _, hX⟩ ↦
    (isInner_iff_forall_pointNorm_lt hB).mpr
      ⟨n, ψ, hψ, hφ, fun i y hy ↦ (hX i y hy).trans_lt hε1⟩⟩
  let s (i : Fin n) : ℝ := supSeminorm K (U.toSections (ψ ⟨X i, isRestricted_X _ i⟩))
  obtain ⟨m, hm, hval⟩ := U.isAffinoidAlgebra.exists_supSeminorm_pow_eq_norm
  obtain ⟨ϖ, hϖ0, hϖ1⟩ := NormedField.exists_norm_lt_one K
  -- The bound is the largest supremum norm of a generator, or `‖ϖ‖` if all of them are smaller.
  obtain ⟨ε, hε0, hε1, hεval, hsε⟩ : ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧
      (∃ m : ℕ, 0 < m ∧ ∃ c : Kˣ, ε ^ m = ‖(c : K)‖) ∧ ∀ i, s i ≤ ε := by
    by_cases h : ∃ i, ‖ϖ‖ < s i
    · obtain ⟨i₁, hi₁⟩ := h
      have : Nonempty (Fin n) := ⟨i₁⟩
      obtain ⟨i, hi⟩ := Finite.exists_max s
      have hpos : 0 < s i := hϖ0.trans (hi₁.trans_le (hi i₁))
      obtain ⟨c, hc⟩ := hval (U.toSections (ψ ⟨X i, isRestricted_X _ i⟩))
      have hc0 : c ≠ 0 := norm_pos_iff.mp (hc ▸ pow_pos hpos m)
      exact ⟨s i, hpos, hX i, ⟨m, hm, Units.mk0 c hc0, hc⟩, hi⟩
    · simp only [not_exists, not_lt] at h
      exact ⟨‖ϖ‖, hϖ0, hϖ1, ⟨1, one_pos, Units.mk0 ϖ (norm_pos_iff.mp hϖ0), by simp⟩, h⟩
  exact ⟨n, ψ, hψ, hφ, ε, hε0, hε1, hεval, fun i ↦
    (supSeminorm_toSections_le_iff hB U _ hε0.le).mp (hsε i)⟩

/-- **The relative-polydisc criterion.** `U ⋐_A Sp B` exactly when some closed immersion of
`Sp B` into the relative unit polydisc over `Sp A`, given by a surjection
`ψ : A⟨X₁, …, Xₙ⟩ → B` extending `φ`, maps `U` into the relative polydisc
`{|X₁|, …, |Xₙ| ≤ ε}` for some `ε` with `0 < ε < 1` in the divisible hull of the value group. -/
theorem isInner_iff_exists_mapsTo (hB : IsAffinoidAlgebra K B) :
    U.IsInner φ ↔ ∃ (n : ℕ) (ψ : IsRestricted.subring (R := A) (fun _ : Fin n ↦ 1) →ₐ[K] B),
      Function.Surjective ψ ∧ (∀ a, ψ (algebraMap A _ a) = φ a) ∧
        ∃ ε : ℝ, 0 < ε ∧ ε < 1 ∧ (∃ m : ℕ, 0 < m ∧ ∃ c : Kˣ, ε ^ m = ‖(c : K)‖) ∧
          Set.MapsTo (hB.maximalSpectrumComap ψ) U
            {z | ∀ i, pointNorm K z ⟨X i, isRestricted_X _ i⟩ ≤ ε} := by
  simp only [isInner_iff_exists_pointNorm_le hB, Set.MapsTo, Set.mem_ofPred_eq,
    IsAffinoidAlgebra.pointNorm_maximalSpectrumComap, SetLike.mem_coe]
  exact exists₂_congr fun _ _ ↦ and_congr_right' <| and_congr_right' <| exists_congr fun _ ↦
    and_congr_right' <| and_congr_right' <| and_congr_right'
      ⟨fun h _ hy i ↦ h i _ hy, fun h i _ hy ↦ h hy i⟩

/-- **Relative compactness passes to smaller subdomains.** If `U ⋐_A Sp B` and `V ⊆ U` is an
affinoid subdomain, then `V ⋐_A Sp B`. -/
theorem IsInner.anti (hB : IsAffinoidAlgebra K B) (h : U.IsInner φ)
    {V : AffinoidSubdomain K B} (hVU : V ≤ U) : V.IsInner φ := by
  obtain ⟨n, ψ, hψ, hφ, hX⟩ := (isInner_iff_forall_pointNorm_lt hB).mp h
  exact (isInner_iff_forall_pointNorm_lt hB).mpr ⟨n, ψ, hψ, hφ, fun i y hy ↦ hX i y (hVU hy)⟩

/-- **The empty subdomain is inner.** Over an affinoid base `A`, the empty affinoid subdomain of
`Sp B` is relatively compact. The content is the existence of a presentation of `B` by restricted
series over `A` extending `φ`. -/
theorem isInner_empty [CompleteSpace A] (hA : IsAffinoidAlgebra K A) (hB : IsAffinoidAlgebra K B)
    (φ : A →ₐ[K] B) :
    (empty hB).IsInner φ := by
  obtain ⟨n, ψ, hψ, hφ⟩ := hA.exists_surjective_algHom_isRestricted_subring hB φ
  exact (isInner_iff_forall_pointNorm_lt hB).mpr
    ⟨n, ψ, hψ, hφ, fun _ y hy ↦ absurd hy (not_mem_empty hB y)⟩

/-- **Finite affinoids are inner in themselves.** If `φ : A → B` is a finite homomorphism of
affinoid algebras, then the whole of `Sp B` is relatively compact over `A`. -/
theorem isInner_univ_of_finite [CompleteSpace A] (hA : IsAffinoidAlgebra K A)
    (hB : IsAffinoidAlgebra K B) (hφ : φ.Finite) : (univ hB).IsInner φ := by
  classical
  -- Equip `B` with a complete algebra norm, to apply the universal property of `A⟨X⟩`.
  let := hB.residueNormedCommRing
  let := hB.residueNormedAlgebra
  have := hB.isUltrametricDist_residueNormedCommRing
  have := hB.completeSpace_residueNormedCommRing
  let := φ.toRingHom.toAlgebra
  have : Module.Finite A B := hφ
  obtain ⟨n, g, hg⟩ := Module.Finite.exists_fin' A B
  let b (i : Fin n) : B := g (Pi.single i 1)
  -- Scale the module generators `b i` to supremum norm less than one.
  set M : ℝ := 1 + ∑ i, supSeminorm K (b i)
  have hM : 0 < M := add_pos_of_pos_of_nonneg one_pos
    (Finset.sum_nonneg fun i _ ↦ supSeminorm_nonneg (K := K) (b i))
  obtain ⟨c, hc0, hc⟩ := NormedField.exists_norm_lt K (inv_pos.mpr hM)
  have hcb (i : Fin n) : supSeminorm K (c • b i) < 1 := by
    rw [supSeminorm_smul]
    have hbM : supSeminorm K (b i) ≤ M := by
      have := Finset.single_le_sum (fun j _ ↦ supSeminorm_nonneg (K := K) (b j)) (Finset.mem_univ i)
      linarith
    calc ‖c‖ * supSeminorm K (b i) ≤ ‖c‖ * M := by gcongr
      _ < M⁻¹ * M := by gcongr
      _ = 1 := inv_mul_cancel₀ hM.ne'
  have hpb (i : Fin n) : Huber.IsPowerBounded (c • b i) :=
    hB.isPowerBounded_iff_supSeminorm_le_one.mpr (hcb i).le
  refine (isInner_iff_forall_pointNorm_lt hB).mpr ⟨n, hA.restrictedLift hB φ hpb, fun y ↦ ?_,
    IsAffinoidAlgebra.restrictedLift_algebraMap hA hB φ hpb, fun i y _ ↦ ?_⟩
  · -- `y = ∑ aᵢ bᵢ` is the image of `∑ aᵢ c⁻¹ Xᵢ`.
    obtain ⟨v, rfl⟩ := hg y
    have hc : c ≠ 0 := norm_pos_iff.mp hc0
    refine ⟨∑ i, algebraMap A (IsRestricted.subring (R := A) (fun _ : Fin n ↦ 1)) (v i) *
      c⁻¹ • ⟨X i, isRestricted_X _ i⟩, ?_⟩
    have hgv : g v = ∑ i, v i • b i := by
      simp only [b, ← map_smul, ← map_sum]
      congr 1
      ext j
      simp [Pi.single_apply]
    rw [hgv, map_sum]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [map_mul, IsAffinoidAlgebra.restrictedLift_algebraMap, map_smul,
      IsAffinoidAlgebra.restrictedLift_X, inv_smul_smul₀ hc]
    exact (Algebra.smul_def (v i) (b i)).symm
  · rw [IsAffinoidAlgebra.restrictedLift_X]
    exact (hB.pointNorm_le_supSeminorm y _).trans_lt (hcb i)

end Inner

section Reduction

variable {B : Type u} [CommRing B] [Algebra K B]

local notation "Tate " n:max => IsRestricted.subring (R := K) (fun _ : Fin n ↦ 1)

/-- **Inner over the base field forces an integral reduction.** If the whole of `Sp B` is
relatively compact over `K`, then every `f : B` with `|f|sup ≤ 1` is a root of a monic polynomial
with coefficients in the unit ball of `K` up to an element of supremum norm less than one: the
canonical reduction of `B` is integral over the residue field of `K`. -/
theorem IsInner.exists_monic_supSeminorm_aeval_lt_one (hB : IsAffinoidAlgebra K B)
    (h : (univ hB).IsInner (Algebra.ofId K B)) {f : B} (hf : supSeminorm K f ≤ 1) :
    ∃ q : K[X], q.Monic ∧ (∀ j, ‖q.coeff j‖ ≤ 1) ∧ supSeminorm K (aeval f q) < 1 := by
  obtain ⟨n, ψ, hψ, -, ε, hε0, hε1, -, hX⟩ := (isInner_iff_exists_pointNorm_le hB).mp h
  have hXε (i : Fin n) : supSeminorm K (ψ ⟨X i, isRestricted_X _ i⟩) ≤ ε :=
    (hB.supSeminorm_le_iff hε0.le).mpr fun y ↦ hX i y (mem_univ hB y)
  -- `f` is integral over the image `B₀` of the Gauss unit ball, by a monic equation `P`.
  let T₀ := Subring.unitClosedBall (Tate n)
  let ρ : T₀ →+* T₀.map ψ.toRingHom :=
    ψ.toRingHom.restrict _ _ fun g hg ↦ ⟨g, hg, rfl⟩
  have hρ : Function.Surjective ρ := by
    rintro ⟨_, g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  obtain ⟨P, hPm, hP⟩ := (ψ.isIntegral_map_unitClosedBall_iff_supSeminorm_le_one hψ).mpr hf
  -- Lift `P` to a monic `Q` over the Gauss unit ball and take constant coefficients.
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_natDegree_eq_and_monic
    ((mem_lifts P).mpr (Polynomial.map_surjective ρ hρ P)) hPm
  let κ : T₀ →+* K := constantCoeff.comp ((IsRestricted.subring _).subtype.comp T₀.subtype)
  refine ⟨Q.map κ, hQm.map κ, fun j ↦ ?_, ?_⟩
  · rw [Polynomial.coeff_map]
    exact (norm_constantCoeff_le _).trans (Subring.mem_unitClosedBall.mp (Q.coeff j).2)
  -- `q(f) = ∑ (κ Qⱼ - ψ Qⱼ) fʲ` since `P(f) = 0`, and each term is at most `ε`.
  have hP0 : ∑ j ∈ Finset.range (Q.natDegree + 1), ψ (Q.coeff j) * f ^ j = 0 := by
    rw [← hP, ← hQ, eval₂_map, eval₂_eq_sum_range]
    rfl
  have hq : aeval f (Q.map κ) = -∑ j ∈ Finset.range (Q.natDegree + 1),
      (ψ (Q.coeff j) - algebraMap K B (κ (Q.coeff j))) * f ^ j := by
    rw [aeval_def, eval₂_map, eval₂_eq_sum_range]
    simp only [sub_mul, Finset.sum_sub_distrib, hP0, zero_sub, neg_neg, RingHom.comp_apply]
  rw [hq, supSeminorm_neg]
  refine lt_of_le_of_lt ?_ hε1
  refine Finset.sum_induction _ (fun b ↦ supSeminorm K b ≤ ε)
    (fun a b ha hb ↦ (hB.supSeminorm_add_le a b).trans (max_le ha hb))
    (supSeminorm_zero.trans_le hε0.le) fun j _ ↦ ?_
  have hj := hB.supSeminorm_map_sub_algebraMap_constantCoeff_le ψ hε0 hε1.le hXε
    (Subring.mem_unitClosedBall.mp (Q.coeff j).2)
  have hfj : supSeminorm K (f ^ j) ≤ 1 := supSeminorm_le zero_le_one fun y ↦ by
    rw [y.pointNorm_pow]
    exact pow_le_one₀ (pointNorm_nonneg f) ((hB.pointNorm_le_supSeminorm y f).trans hf)
  exact (hB.supSeminorm_mul_le _ _).trans
    ((mul_le_mul hj hfj (supSeminorm_nonneg _) hε0.le).trans_eq (mul_one ε))

/-- **The closed unit polydisc is not inner in itself.** For `n ≥ 1`, the spectrum of the Tate
algebra `K⟨X₁, …, Xₙ⟩` is not relatively compact in itself over `K`. In contrast, finite
`K`-algebras are inner in themselves (`TauCeti.AffinoidSubdomain.isInner_univ_of_finite`). -/
theorem not_isInner_univ_tate {n : ℕ} [NeZero n] :
    ¬ (univ (isAffinoidAlgebra_tate (K := K) (σ := Fin n))).IsInner (Algebra.ofId K (Tate n)) := by
  classical
  intro h
  let x : Tate n := ⟨X 0, isRestricted_X _ 0⟩
  obtain ⟨q, hqm, -, hq⟩ := h.exists_monic_supSeminorm_aeval_lt_one isAffinoidAlgebra_tate
    (f := x) (by rw [MvPowerSeries.supSeminorm_eq_norm, MvPowerSeries.norm_X])
  -- The coefficient of `X₀ ^ deg q` in `q(X₀)` is the leading coefficient `1`.
  have hcoeff : coeff (Finsupp.single 0 q.natDegree) (aeval x q : MvPowerSeries (Fin n) K) = 1 := by
    rw [aeval_eq_sum_range]
    simp [x, MvPowerSeries.coeff_X_pow, (Finsupp.single_injective _).eq_iff, hqm.coeff_natDegree]
  rw [MvPowerSeries.supSeminorm_eq_norm] at hq
  have := norm_coeff_le_norm (aeval x q) (Finsupp.single 0 q.natDegree)
  rw [hcoeff, norm_one] at this
  exact hq.not_ge this

end Reduction

end AffinoidSubdomain

end TauCeti
