/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import TauCeti.Algebra.Lie.UniversalEnveloping.Kostant.RootSubgroup.Triangular
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Borel

/-!
# Injectivity and distinctness of root subgroups of a Chevalley datum

For any `TauCeti.DynkinType.ChevalleyDatum`, we prove pointwise root-subgroup faithfulness and
separation: `rootSubgroupPoints_injective`, `rootSubgroupPoints_inj`,
`rootSubgroupPoints_eq_one_iff`, and `inf_range_rootSubgroupPoints_reflectionPerm_self_eq_bot` over
every commutative ring, and `rootSubgroupPoints_ofAdd_one_mem_range_iff`,
`exists_rootSubgroupPoints_eq_ofAdd_one_iff`, `range_rootSubgroupPoints_le_iff`,
`range_rootSubgroupPoints_injective`, and `range_rootSubgroupPoints_inj` over every nontrivial
commutative ring. For the scheme-level closed-immersion result on
`TauCeti.DynkinType.scChevalleyDatum` over `ℤ`, see
`TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.ClosedImmersion`
(`TauCeti.DynkinType.isClosedImmersion_rootSubgroup_scChevalleyDatum`).

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Ch. 3, Lemmas 17–19; *Endomorphisms of linear
  algebraic groups*, Mem. Amer. Math. Soc. **80** (1968), §§10–11.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum
open Multiplicative TauCeti.UniversalEnvelopingAlgebra
universe v
variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-! ## Injectivity of root subgroups -/

private noncomputable abbrev simpleOp (i : Fin t.rank) :=
  D.representation (_root_.UniversalEnvelopingAlgebra.ι ℚ ((t.lieBasis ht).rootGenerator (.inl i)))

private noncomputable def simpleDivPowEnd (i : Fin t.rank) (n : ℕ) : Module.End ℤ D.lattice :=
  integralDividedPower (D.simpleOp i) D.lattice n fun _ hv =>
    dividedPower_apply_mem_of_kostantForm_apply_mem (t.lieBasis ht).rootGenerator
      (t.lieBasis ht).h D.representation D.representation_mem_lattice (.inl i) n hv

private noncomputable def simpleDivPowMat (i : Fin t.rank) (n : ℕ) :
    Matrix (Fin D.dim) (Fin D.dim) ℤ := LinearMap.toMatrixAlgEquiv D.basis (D.simpleDivPowEnd i n)

private theorem simpleDivPowMat_pow (i : Fin t.rank) (n : ℕ) :
    D.simpleDivPowMat i 1 ^ n = n.factorial • D.simpleDivPowMat i n := by
  have hend : ∀ m, D.simpleDivPowEnd i 1 ^ m = m.factorial • D.simpleDivPowEnd i m := Nat.rec
    (by simp [simpleDivPowEnd]) fun m ih => by
      rw [pow_succ, ih, smul_mul_assoc, simpleDivPowEnd, simpleDivPowEnd, mul_integralDividedPower,
        smul_smul, Nat.choose_succ_self_right, Nat.factorial_succ, mul_comm]
      -- Both sides are `(m + 1)! • integralDividedPower ... (m + 1)`, differing only in the
      -- proof-irrelevant lattice-invariance proof inside `simpleDivPowEnd i (m + 1)`.
      rfl
  simpa only [simpleDivPowMat, map_pow, map_nsmul]
    using congrArg (LinearMap.toMatrixAlgEquiv D.basis) (hend n)

private theorem simpleDivPowMat_eq_zero_of_weight_ne (i : Fin t.rank) {r s : Fin D.dim} {n : ℕ}
    (hrs : D.weight r ≠
      D.weight s + n • (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i)) :
    D.simpleDivPowMat i n r s = 0 := by
  rw [simpleDivPowMat, LinearMap.toMatrixAlgEquiv_apply, simpleDivPowEnd]
  exact repr_integralDividedPower_eq_zero_of_weight_ne (t.lieBasis ht).rootGenerator
    (t.lieBasis ht).h D.representation D.lattice D.representation_mem_lattice D.basis D.weight
    D.isCartanWeightVector_basis (fun j => by
      rw [t.lie_lieBasis_h_rootGenerator ht (.inl i) j,
        t.rootGeneratorWeight_inl_eq_root_simpleIndex ht i]) hrs

private theorem simpleRootSubgroup_matrix_eq_sum (i : Fin t.rank) (A : Type*) [CommRing A]
    (u : A) : ((D.rootSubgroupPoints (t.simpleIndex ht i) A (ofAdd u) :
        Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A) =
      ∑ k ∈ Finset.range (nilpotencyClass (D.simpleOp i) + 2),
        u ^ k • (D.simpleDivPowMat i k).map (Int.cast : ℤ → A) := by
  rw [D.coe_rootSubgroupPoints_simpleIndex]
  simpa only [MulEquiv.apply_symm_apply, toAdd_ofAdd] using
    kostantRootSubgroupMatrix_eq_sum (t.lieBasis ht).rootGenerator (t.lieBasis ht).h
      D.representation D.lattice D.representation_mem_lattice (.inl i)
      (D.isNilpotent_representation_rootGenerator (.inl i)) D.basis
      (nilpotencyClass (D.simpleOp i) + 2) (D.simpleDivPowMat i) (Nat.le_add_right _ 2)
      (fun k _ s => by
        rw [← D.basis.sum_repr (integralDividedPower _ D.lattice k _ (D.basis s))]
        exact Finset.sum_congr rfl fun r _ => by
          simp only [simpleDivPowMat, simpleDivPowEnd, LinearMap.toMatrixAlgEquiv_apply])
      ((AdditiveGroup.gaPointsMulEquiv (R := ℤ) (A := A)).symm (ofAdd u))

private theorem dvd_matrix_of_pow_eq_factorial_nsmul {m : Type*} [Fintype m] [DecidableEq m]
    (M : ℕ → Matrix m m ℤ) (hpow : ∀ n, M 1 ^ n = n.factorial • M n)
    {p : ℕ} (hp : p.Prime) (hdiv : ∀ r s, (p : ℤ) ∣ M 1 r s)
    {n : ℕ} (hn : n ≠ 0) (r s : m) : (p : ℤ) ∣ M n r s := by
  have hpow_div : ∀ k r s, (p : ℤ) ^ k ∣ (M 1 ^ k) r s := Nat.rec
    (fun _ _ => by simp) fun k ih r s => by
      rw [pow_succ, pow_succ, Matrix.mul_apply]
      exact Finset.dvd_sum fun l _ => mul_dvd_mul (ih r l) (hdiv l s)
  have : Fact p.Prime := ⟨hp⟩
  have hdvdN : p ^ n ∣ n.factorial * (M n r s).natAbs := by
    rw [← Int.natCast_dvd_natCast, Nat.cast_mul, Nat.cast_pow]
    simpa only [hpow n, Matrix.smul_apply, nsmul_eq_mul, Int.natAbs_mul,
      Int.natAbs_natCast, Nat.cast_mul] using Int.dvd_natAbs.mpr (hpow_div n r s)
  by_contra hndvd
  have hcop := (hp.coprime_iff_not_dvd.mpr fun h => hndvd (Int.natCast_dvd.mpr h)).pow_left n
  have hfin := Nat.finiteMultiplicity_iff.mpr ⟨hp.ne_one, Nat.factorial_pos n⟩
  exact (not_lt_of_ge (hfin.pow_dvd_iff_le_multiplicity.mp (hcop.dvd_of_dvd_mul_right hdvdN)))
    (multiplicity_factorial_lt_of_ne_zero p hn)

private theorem exists_bezout_simpleDivPowMat_one (i : Fin t.rank) :
    ∃ c : Fin D.dim × Fin D.dim → ℤ,
      ∑ pq : Fin D.dim × Fin D.dim, c pq * D.simpleDivPowMat i 1 pq.1 pq.2 = 1 := by
  let I : Ideal ℤ := Ideal.span (Set.range fun pq : Fin D.dim × Fin D.dim =>
    D.simpleDivPowMat i 1 pq.1 pq.2)
  have hI : I = ⊤ := by_contra fun hne => by
    let d := Submodule.IsPrincipal.generator I
    have hd r s : d ∣ D.simpleDivPowMat i 1 r s :=
      (Submodule.IsPrincipal.mem_iff_generator_dvd I).mp (Ideal.subset_span ⟨(r, s), rfl⟩)
    have hd1 : d.natAbs ≠ 1 := fun h1 => hne (by
      rw [← Submodule.IsPrincipal.span_singleton_generator I, Ideal.span_singleton_eq_top]
      exact Int.isUnit_iff_natAbs_eq.mpr h1)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hd1
    have : Fact p.Prime := ⟨hp⟩
    have hdiv_all {n : ℕ} (hn : n ≠ 0) (r s : Fin D.dim) :
        (p : ℤ) ∣ D.simpleDivPowMat i n r s :=
      dvd_matrix_of_pow_eq_factorial_nsmul (D.simpleDivPowMat i)
        (D.simpleDivPowMat_pow i) hp (fun r' s' => (Int.natCast_dvd.mpr hpd).trans (hd r' s'))
        hn r s
    refine D.rootSubgroupPoints_ofAdd_one_ne_one (ZMod p) (t.simpleIndex ht i)
      (Subtype.ext (Matrix.GeneralLinearGroup.ext fun r s => ?_))
    rw [D.simpleRootSubgroup_matrix_eq_sum i (ZMod p) 1, Finset.sum_range_succ']
    have hM0 : D.simpleDivPowMat i 0 = 1 := by simp [simpleDivPowMat, simpleDivPowEnd]
    have hsum0 : ∑ k ∈ Finset.range (nilpotencyClass (D.simpleOp i) + 1),
        ((1 : ZMod p) ^ (k + 1) • (D.simpleDivPowMat i (k + 1)).map
          (Int.cast : ℤ → ZMod p)) r s = 0 := Finset.sum_eq_zero fun k _ => by
      simpa only [one_pow, one_smul, Matrix.map_apply] using
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr (hdiv_all (Nat.succ_ne_zero k) r s)
    rw [Matrix.add_apply, Matrix.sum_apply, hsum0]; simp [hM0]
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (by rw [hI]; trivial : (1 : ℤ) ∈ I)
  exact ⟨c, by simpa only [smul_eq_mul] using hc⟩

private theorem rootSubgroupPoints_simpleIndex_injective (A : Type v) [CommRing A]
    (i : Fin t.rank) : Function.Injective (D.rootSubgroupPoints (t.simpleIndex ht i) A) := by
  obtain ⟨c, hc⟩ := D.exists_bezout_simpleDivPowMat_one i
  let α := (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i)
  let S := Finset.univ.filter fun pq : Fin D.dim × Fin D.dim => D.weight pq.1 = D.weight pq.2 + α
  let mat (u : A) : Matrix (Fin D.dim) (Fin D.dim) A :=
    ((D.rootSubgroupPoints (t.simpleIndex ht i) A (ofAdd u) :
      Matrix.GeneralLinearGroup (Fin D.dim) A) : Matrix (Fin D.dim) (Fin D.dim) A)
  have hcS : ∑ pq ∈ S, c pq * D.simpleDivPowMat i 1 pq.1 pq.2 = 1 := by
    rw [← hc]; refine Finset.sum_subset (Finset.subset_univ S) fun pq _ hpq => by
      rw [D.simpleDivPowMat_eq_zero_of_weight_ne i
        (by simpa only [S, Finset.mem_filter, Finset.mem_univ, true_and, one_smul] using hpq),
        mul_zero]
  have hentry (u : A) {pq} (hpq : pq ∈ S) :
      mat u pq.1 pq.2 = u * (D.simpleDivPowMat i 1 pq.1 pq.2 : A) := by
    have hwt : D.weight pq.1 = D.weight pq.2 + α := (Finset.mem_filter.mp hpq).2
    dsimp only [mat]
    rw [D.simpleRootSubgroup_matrix_eq_sum i A u, Matrix.sum_apply, Finset.sum_eq_single 1]
    · simp only [pow_one, Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
    · intro k _ hk1
      have hne : D.weight pq.1 ≠ D.weight pq.2 + k • α := fun heq => hk1 (by
        have h1k : 1 • α = k • α := add_left_cancel (by rw [one_smul, ← hwt, heq])
        have h0 : (1 : ℤ) - k = 0 := (smul_eq_zero.mp (by
          rw [sub_smul, one_smul, natCast_zsmul, ← h1k, one_smul, sub_self])).resolve_right
          ((t.simplyConnectedRootDatum ht).ne_zero _)
        omega)
      simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul,
        D.simpleDivPowMat_eq_zero_of_weight_ne i hne, Int.cast_zero, mul_zero]
    · exact fun habs => (habs (Finset.mem_range.mpr (by omega))).elim
  have hrecover (u : A) : ∑ pq ∈ S, (c pq : A) * mat u pq.1 pq.2 = u := by
    conv_rhs => rw [← mul_one u, ← Int.cast_one (R := A), ← hcS, Int.cast_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun pq hpq => by rw [hentry u hpq, Int.cast_mul]; ring
  intro u₁ u₂ h; refine toAdd.injective ?_
  rw [← hrecover (toAdd u₁), ← hrecover (toAdd u₂)]; simp only [mat, ofAdd_toAdd, h]

/-- **Every root subgroup of a Chevalley datum is injective over every commutative ring.** -/
theorem rootSubgroupPoints_injective (A : Type v) [CommRing A] (γ : Fin t.numRoots) :
    Function.Injective (D.rootSubgroupPoints γ A) :=
  D.rootSubgroupPoints_injective_of_simple A (D.rootSubgroupPoints_simpleIndex_injective A) γ

/-- Equality of elements in a root subgroup is equivalent to equality of their parameters. -/
@[simp] theorem rootSubgroupPoints_inj (A : Type v) [CommRing A] (γ : Fin t.numRoots)
    {u v : Multiplicative A} : D.rootSubgroupPoints γ A u = D.rootSubgroupPoints γ A v ↔ u = v :=
  (D.rootSubgroupPoints_injective A γ).eq_iff

/-- A root-subgroup element is trivial if and only if its parameter is `1`. -/
-- Not @[simp]: together with `@[simp] rootSubgroupPoints_ofAdd_one_ne_one` it fails `simpNF`.
theorem rootSubgroupPoints_eq_one_iff (A : Type v) [CommRing A] (γ : Fin t.numRoots)
    (u : Multiplicative A) : D.rootSubgroupPoints γ A u = 1 ↔ u = 1 :=
  map_eq_one_iff (D.rootSubgroupPoints γ A) (D.rootSubgroupPoints_injective A γ)

/-! ## Trivial intersection of opposite root subgroups and distinctness -/

/-- **Opposite root subgroups intersect trivially over every commutative ring.** -/
@[simp] theorem inf_range_rootSubgroupPoints_reflectionPerm_self_eq_bot (A : Type v) [CommRing A]
    (γ : Fin t.numRoots) : (D.rootSubgroupPoints γ A).range ⊓
      (D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm γ γ) A).range = ⊥ := by
  let P := t.simplyConnectedRootDatum ht
  have hpos {δ} (hd : δ ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht)) {g : D.points A}
      (hg : g ∈ (D.rootSubgroupPoints δ A).range)
      (hg' : g ∈ (D.rootSubgroupPoints (P.reflectionPerm δ δ) A).range) : g = 1 := by
    obtain ⟨u, rfl⟩ := hg; obtain ⟨v, hv⟩ := hg'
    exact hv ▸ (D.rootSubgroupPoints_mem_borelSubgroup_iff_of_mem_negRoots A
      (by rw [← t.reflectionPerm_rationalRootSystem ht]
          exact (reflectionPerm_self_mem_negRoots_iff_mem_posRoots _ _ _).mpr hd) v).mp
      (hv ▸ D.positivePoints_le_borelSubgroup A (D.rootSubgroupPoints_mem_positivePoints A hd u))
  rw [Subgroup.eq_bot_iff_forall]; rintro g ⟨hg, hg'⟩
  rcases mem_posRoots_or_mem_negRoots (t.rationalRootSystem ht) (t.rationalBase ht) γ with h | h
  · exact hpos h hg hg'
  · refine hpos (by rw [← t.reflectionPerm_rationalRootSystem ht,
      reflectionPerm_self_mem_posRoots_iff_mem_negRoots]; exact h) hg'
      (by have := reflectionPerm_self_involutive P γ; dsimp [P] at this; rwa [this])

private theorem eq_of_rootSubgroupPoints_ofAdd_one_mem_range (K : Type v) [Field K] [Infinite K]
    {α β : Fin t.numRoots}
    (hmem : D.rootSubgroupPoints α K (ofAdd 1) ∈ (D.rootSubgroupPoints β K).range) : α = β := by
  obtain ⟨b, hb⟩ := hmem
  have hb0 : toAdd b ≠ 0 := fun h0 => D.rootSubgroupPoints_ofAdd_one_ne_one K α
    (by rw [← hb, toAdd.injective (h0.trans toAdd_one.symm), map_one])
  obtain ⟨d, hd, z, hz⟩ := exists_nsmul_eq_zsmul_of_torusCharacter_eq_one_imp
    (ξ := D.coordinateRoot α) (η := D.coordinateRoot β) fun s hs => by
      have hconj := congrArg (fun g => D.torusPoints K s * g * (D.torusPoints K s)⁻¹) hb
      rw [← ofAdd_toAdd b, D.torusPoints_conj_rootSubgroupPoints,
        D.torusPoints_conj_rootSubgroupPoints, hs, Units.val_one, one_mul, ← hb] at hconj
      exact Units.ext (mul_right_cancel₀ hb0
        (by simpa using congrArg toAdd (D.rootSubgroupPoints_injective K β hconj)))
  rcases D.eq_or_eq_reflectionPerm_of_zsmul_coordinateRoot_eq (b := z)
      (Int.natCast_ne_zero.mpr hd.ne') (by simpa only [natCast_zsmul] using hz) with rfl | rfl
  · rfl
  · exact (D.rootSubgroupPoints_ofAdd_one_ne_one K α (Subgroup.mem_bot.mp
      ((D.inf_range_rootSubgroupPoints_reflectionPerm_self_eq_bot K α).symm ▸
        ⟨⟨ofAdd 1, rfl⟩, ⟨b, hb⟩⟩))).elim

/-- **Over any nontrivial commutative ring, `x_α(1)` belongs to the `β`-root subgroup iff
`α = β`.** -/
-- Not @[simp]: the LHS simplifies via `MonoidHom.mem_range` and `Multiplicative.exists`.
theorem rootSubgroupPoints_ofAdd_one_mem_range_iff (A : Type v) [CommRing A] [Nontrivial A]
    {α β : Fin t.numRoots} :
    D.rootSubgroupPoints α A (ofAdd 1) ∈ (D.rootSubgroupPoints β A).range ↔ α = β :=
  ⟨fun ⟨b, hb⟩ => by
    obtain ⟨𝔪, _⟩ := Ideal.exists_maximal A
    let _ : Field (A ⧸ 𝔪) := Ideal.Quotient.field 𝔪; let K := AlgebraicClosure (A ⧸ 𝔪)
    have hmap := congrArg ((D.pointsPresentation A).map (D.pointsPresentation K)
      ((algebraMap (A ⧸ 𝔪) K).comp (Ideal.Quotient.mk 𝔪))) hb
    rw [D.map_rootSubgroupPoints, D.map_rootSubgroupPoints, toAdd_ofAdd, map_one] at hmap
    exact D.eq_of_rootSubgroupPoints_ofAdd_one_mem_range K ⟨_, hmap⟩,
   fun h => h ▸ ⟨ofAdd 1, rfl⟩⟩

/-- **Over any nontrivial commutative ring, `x_α(1)` lies in the image of `x_β` iff `α = β`
(normal form after `simp` expands `MonoidHom.mem_range`).** -/
@[simp] theorem exists_rootSubgroupPoints_eq_ofAdd_one_iff (A : Type v) [CommRing A] [Nontrivial A]
    {α β : Fin t.numRoots} :
    (∃ a : A, D.rootSubgroupPoints β A (ofAdd a) = D.rootSubgroupPoints α A (ofAdd 1)) ↔
      α = β := by
  simpa only [MonoidHom.mem_range, Multiplicative.exists] using
    D.rootSubgroupPoints_ofAdd_one_mem_range_iff A (α := α) (β := β)

/-- **Over any nontrivial commutative ring, one root subgroup is contained in another only at the
same root.** -/
@[simp] theorem range_rootSubgroupPoints_le_iff (A : Type v) [CommRing A] [Nontrivial A]
    {α β : Fin t.numRoots} :
    (D.rootSubgroupPoints α A).range ≤ (D.rootSubgroupPoints β A).range ↔ α = β :=
  ⟨fun hle => (D.rootSubgroupPoints_ofAdd_one_mem_range_iff A).mp (hle ⟨ofAdd 1, rfl⟩),
   fun h => h ▸ le_rfl⟩

/-- **Over any nontrivial commutative ring, distinct root indices give distinct root subgroups.** -/
theorem range_rootSubgroupPoints_injective (A : Type v) [CommRing A] [Nontrivial A] :
    Function.Injective fun α : Fin t.numRoots => (D.rootSubgroupPoints α A).range :=
  fun _ _ h => (D.range_rootSubgroupPoints_le_iff A).mp h.le

/-- Over any nontrivial commutative ring, two root subgroups coincide iff they share a root. -/
@[simp] theorem range_rootSubgroupPoints_inj (A : Type v) [CommRing A] [Nontrivial A]
    {α β : Fin t.numRoots} :
    (D.rootSubgroupPoints α A).range = (D.rootSubgroupPoints β A).range ↔ α = β :=
  (D.range_rootSubgroupPoints_injective A).eq_iff

end TauCeti.DynkinType.ChevalleyDatum
