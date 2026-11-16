/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.Basic
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Gauss
import TauCeti.Algebra.AlgebraicGroup.Chevalley.HomExt
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Opposite
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Injective

/-!
# Rigidity and torus conjugacy of standard endomorphisms

Over an infinite field `K` with divisible units (in particular an algebraically closed field),
two standard endomorphisms `F` and `F'` of the points of a Chevalley datum `D` that share the
same injective character map `φ` agree on `D.rootTorusSubgroup K` up to conjugation by a torus
point (`ChevalleyDatum.exists_torusPoints_conj_eq_on_rootTorusSubgroup`).

The proof combines three ingredients:
* the root permutation and field automorphisms on root subgroups extracted from `φ` in
  `TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.Basic`, together with linear
  independence of the simple coordinate roots
  (`ChevalleyDatum.linearIndependent_coordinateRoot_simpleIndex`), which provides a torus point `s`
  matching the scalar ratios on the positive simple roots;
* a rank-one normalizer computation over any infinite field
  (`ChevalleyDatum.mul_eq_one_of_weylProduct_mem_normalizer_range_torusPoints`), proved using
  Gauss factorization (`ChevalleyDatum.rootSubgroupPoints_mul_opposite_eq_gauss`) and opposite-root
  disjointness
  (`ChevalleyDatum.positiveSubgroup_inf_negativeSubgroup_sup_range_kostantTorusPoints_eq_bot`),
  forcing the product of opposite simple root scalars to be `1`;
* determination of homomorphisms on `D.rootTorusSubgroup K` by the positive and negative simple
  root subgroups (`ChevalleyDatum.rootTorusSubgroup_hom_ext_of_rootable`).

When in addition `1 - φ` is injective, Lang's equation on the torus
(`TauCeti.IsCharacterMap.exists_eq_mul_inv`) promotes left-composition by `Int(s)` to actual
conjugacy `F = Int(u) ∘ F' ∘ Int(u)⁻¹` on `D.rootTorusSubgroup K`
(`ChevalleyDatum.exists_torusPoints_conj_comm_on_rootTorusSubgroup`), specializing to endomorphisms
with `φ ^ n = m • 1` (`m ≠ 0, 1`), and in particular to `φ ^ n = (p ^ r) • 1` (`r > 0`) in positive
characteristic `p`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.mul_eq_one_of_weylProduct_mem_normalizer_range_torusPoints`:
  if `x_β(c) * x_{-β}(-d) * x_β(c)` normalizes the actual torus over an infinite field, then
  `c * d = 1`.
* `TauCeti.DynkinType.ChevalleyDatum.linearIndependent_coordinateRoot_simpleIndex`: the simple
  coordinate roots of any Chevalley datum are `ℤ`-linearly independent.
* `TauCeti.DynkinType.ChevalleyDatum.exists_torusPoints_conj_eq_on_rootTorusSubgroup`: rigidity up
  to the torus for standard endomorphisms with a common injective character map.
* `TauCeti.DynkinType.ChevalleyDatum.exists_torusPoints_conj_comm_on_rootTorusSubgroup`: conjugacy
  by a torus point when `1 - φ` is injective.
* `TauCeti.DynkinType.ChevalleyDatum.exists_torusPoints_eq_mul_inv_of_pow_eq_nsmul_one`: Lang's
  equation on `D.torusPoints` when `φ ^ n = (p ^ r) • 1` with `r > 0` in characteristic `p`.
* `exists_torusPoints_conj_comm_on_rootTorusSubgroup_of_pow_eq_smul_one` and
  `exists_torusPoints_conj_comm_on_rootTorusSubgroup_of_charP`: torus conjugacy when a power of `φ`
  is a nonzero scalar other than `1`, in particular a positive power of a prime characteristic.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80** (1968),
  Theorem 10.1 and §11.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 3 and 10.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open Multiplicative TensorProduct TauCeti.UniversalEnvelopingAlgebra

universe v

attribute [local instance high] Algebra.toModule

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-! ## Rank-one normalizer lemma -/

private theorem rootSubgroupPoints_eq_one_of_opposite_eq_torus_mul {A : Type v} [CommRing A]
    (β : Fin t.numRoots) (u v : Multiplicative A) (r₁ r₂ : Fin t.rank → Aˣ)
    (h : D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm β β) A u =
      D.torusPoints A r₁ * D.rootSubgroupPoints β A v * D.torusPoints A r₂) :
    D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm β β) A u = 1 ∧
      D.rootSubgroupPoints β A v = 1 ∧
      D.torusPoints A (r₁ * r₂) = 1 := by
  let β' := (t.simplyConnectedRootDatum ht).reflectionPerm β β
  let m := Units.map (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).toMonoidHom
  have hm : Function.Injective m :=
    Units.map_injective (LinearMap.toMatrixAlgEquiv (D.basis.baseChange A)).injective
  let x := chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator β' (CommAlgCat.of ℤ A) u
  let y := chevalleyRootSubgroup D.representation D.lattice D.representation_mem_lattice
    D.isNilpotent_representation_rootGenerator β (CommAlgCat.of ℤ A) v
  let t₁ := kostantTorusPoints D.lattice D.basis D.coordinateWeight (CommAlgCat.of ℤ A) r₁
  let t₂ := kostantTorusPoints D.lattice D.basis D.coordinateWeight (CommAlgCat.of ℤ A) r₂
  have hxy : x = t₁ * y * t₂ := by
    apply hm
    simpa only [m, x, y, t₁, t₂, β', MulEquiv.toMonoidHom_eq_coe, map_mul,
      D.coe_rootSubgroupPoints, D.coe_torusPoints, Subgroup.coe_mul,
      basisMatrix_kostantTorusPoints, kostantTorusMatrix_apply] using congrArg Subtype.val h
  let T := (kostantTorusPoints D.lattice D.basis D.coordinateWeight (CommAlgCat.of ℤ A)).range
  have ht₁ : t₁ ∈ T := ⟨r₁, rfl⟩
  have ht₂ : t₂ ∈ T := ⟨r₂, rfl⟩
  have hxy1 : x = 1 ∧ y = 1 := by
    rcases mem_posRoots_or_mem_negRoots (t.rationalRootSystem ht) (t.rationalBase ht) β
      with hβ | hβ
    · have hβ' : β' ∈ negRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
        dsimp only [β']
        rw [← t.reflectionPerm_rationalRootSystem ht]
        exact (reflectionPerm_self_mem_negRoots_iff_mem_posRoots _ _ _).mpr hβ
      have hx_mem : x ∈ D.negativeSubgroup (CommAlgCat.of ℤ A) :=
        D.chevalleyRootSubgroup_mem_negativeSubgroup (CommAlgCat.of ℤ A) hβ' u
      have hy_mem : y ∈ D.positiveSubgroup (CommAlgCat.of ℤ A) :=
        D.chevalleyRootSubgroup_mem_positiveSubgroup (CommAlgCat.of ℤ A) hβ v
      have hxbot : x ∈ (⊥ : Subgroup _) := by
        rw [← D.negativeSubgroup_inf_positiveSubgroup_sup_range_kostantTorusPoints_eq_bot A]
        refine ⟨hx_mem, ?_⟩
        rw [hxy]
        exact Subgroup.mul_mem _
          (Subgroup.mul_mem _ (Subgroup.mem_sup_right ht₁) (Subgroup.mem_sup_left hy_mem))
          (Subgroup.mem_sup_right ht₂)
      have hx1 : x = 1 := Subgroup.mem_bot.mp hxbot
      have hy_eq : y = t₁⁻¹ * t₂⁻¹ := by
        rw [hx1] at hxy
        calc
          y = t₁⁻¹ * (t₁ * y * t₂) * t₂⁻¹ := by group
          _ = t₁⁻¹ * 1 * t₂⁻¹ := by rw [← hxy]
          _ = t₁⁻¹ * t₂⁻¹ := by group
      have hybot : y ∈ (⊥ : Subgroup _) := by
        rw [← D.positiveSubgroup_inf_negativeSubgroup_sup_range_kostantTorusPoints_eq_bot A]
        refine ⟨hy_mem, ?_⟩
        rw [hy_eq]
        exact Subgroup.mul_mem _
          (Subgroup.mem_sup_right (T.inv_mem ht₁)) (Subgroup.mem_sup_right (T.inv_mem ht₂))
      exact ⟨hx1, Subgroup.mem_bot.mp hybot⟩
    · have hβ' : β' ∈ posRoots (t.rationalRootSystem ht) (t.rationalBase ht) := by
        dsimp only [β']
        rw [← t.reflectionPerm_rationalRootSystem ht]
        exact (reflectionPerm_self_mem_posRoots_iff_mem_negRoots _ _ _).mpr hβ
      have hx_mem : x ∈ D.positiveSubgroup (CommAlgCat.of ℤ A) :=
        D.chevalleyRootSubgroup_mem_positiveSubgroup (CommAlgCat.of ℤ A) hβ' u
      have hy_mem : y ∈ D.negativeSubgroup (CommAlgCat.of ℤ A) :=
        D.chevalleyRootSubgroup_mem_negativeSubgroup (CommAlgCat.of ℤ A) hβ v
      have hxbot : x ∈ (⊥ : Subgroup _) := by
        rw [← D.positiveSubgroup_inf_negativeSubgroup_sup_range_kostantTorusPoints_eq_bot A]
        refine ⟨hx_mem, ?_⟩
        rw [hxy]
        exact Subgroup.mul_mem _
          (Subgroup.mul_mem _ (Subgroup.mem_sup_right ht₁) (Subgroup.mem_sup_left hy_mem))
          (Subgroup.mem_sup_right ht₂)
      have hx1 : x = 1 := Subgroup.mem_bot.mp hxbot
      have hy_eq : y = t₁⁻¹ * t₂⁻¹ := by
        rw [hx1] at hxy
        calc
          y = t₁⁻¹ * (t₁ * y * t₂) * t₂⁻¹ := by group
          _ = t₁⁻¹ * 1 * t₂⁻¹ := by rw [← hxy]
          _ = t₁⁻¹ * t₂⁻¹ := by group
      have hybot : y ∈ (⊥ : Subgroup _) := by
        rw [← D.negativeSubgroup_inf_positiveSubgroup_sup_range_kostantTorusPoints_eq_bot A]
        refine ⟨hy_mem, ?_⟩
        rw [hy_eq]
        exact Subgroup.mul_mem _
          (Subgroup.mem_sup_right (T.inv_mem ht₁)) (Subgroup.mem_sup_right (T.inv_mem ht₂))
      exact ⟨hx1, Subgroup.mem_bot.mp hybot⟩
  have hux : D.rootSubgroupPoints β' A u = 1 :=
    Subtype.ext ((D.coe_rootSubgroupPoints β' A u).trans ((congrArg m hxy1.1).trans m.map_one))
  have hvy : D.rootSubgroupPoints β A v = 1 :=
    Subtype.ext ((D.coe_rootSubgroupPoints β A v).trans ((congrArg m hxy1.2).trans m.map_one))
  refine ⟨hux, hvy, ?_⟩
  rw [map_mul]
  simpa only [β', hux, hvy, mul_one] using h.symm

/-- **Rank-one normalizer lemma.** If `x_β(c) * x_{-β}(-d) * x_β(c)` with units `c, d` over an
infinite field normalizes the actual torus, then `c * d = 1`. -/
theorem mul_eq_one_of_weylProduct_mem_normalizer_range_torusPoints
    {K : Type v} [Field K] [Infinite K] (β : Fin t.numRoots) (c d : Kˣ)
    (hnorm : D.rootSubgroupPoints β K (ofAdd (c : K)) *
        D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm β β) K
          (ofAdd (-(d : K))) *
        D.rootSubgroupPoints β K (ofAdd (c : K)) ∈
      Subgroup.normalizer (D.torusPoints K).range) :
    c * d = 1 := by
  by_contra hcd
  have h1cd : (1 : K) - (c : K) * (d : K) ≠ 0 :=
    sub_ne_zero.mpr fun heq => hcd (Units.ext (by
      simpa only [Units.val_mul, Units.val_one] using heq.symm))
  let u : Kˣ := Units.mk0 (1 - (c : K) * (d : K)) h1cd
  let β' := (t.simplyConnectedRootDatum ht).reflectionPerm β β
  let h : Fin t.rank → Kˣ :=
    D.fullWeightTorusRestriction K (fun i => u ^ (t.simplyConnectedRootDatum ht).coroot β i)
  let a : K := -(d : K) * ((u⁻¹ : Kˣ) : K)
  let b : K := (c : K) * ((u⁻¹ : Kˣ) : K) + (c : K)
  let w := D.rootSubgroupPoints β K (ofAdd (c : K)) *
    D.rootSubgroupPoints β' K (ofAdd (-(d : K))) *
    D.rootSubgroupPoints β K (ofAdd (c : K))
  have ha : a ≠ 0 := mul_ne_zero (neg_ne_zero.mpr (Units.ne_zero d)) (Units.ne_zero u⁻¹)
  have hw : w = D.rootSubgroupPoints β' K (ofAdd a) * D.torusPoints K h *
      D.rootSubgroupPoints β K (ofAdd b) := by
    have hg := D.rootSubgroupPoints_mul_opposite_eq_gauss β K (c : K) (-(d : K)) u
      (by simp only [u, Units.val_mk0]; ring)
    dsimp only [w, a, b, h, β']
    rw [hg, mul_assoc, mul_assoc, ← map_mul, ← ofAdd_add, mul_assoc]
  -- Choose a torus point `s` where the root character `β` is nontrivial.
  obtain ⟨s, hs⟩ : ∃ s : Fin t.rank → Kˣ, torusCharacter s (D.coordinateRoot β) ≠ 1 := by
    by_contra hall
    push Not at hall
    have hzero : D.coordinateRoot β = 0 :=
      weightChar_injective (K := K) (MonoidHom.ext fun s => by
        simpa only [weightChar_apply, torusCharacter_zero] using hall s)
    exact D.coordinateRoot_ne_zero β hzero
  have hmem : w * D.torusPoints K s * w⁻¹ ∈ (D.torusPoints K).range :=
    ((Subgroup.mem_normalizer_iff.mp hnorm) (D.torusPoints K s)).mp ⟨s, rfl⟩
  obtain ⟨s', hs'⟩ := hmem
  have hcomm : w * D.torusPoints K s = D.torusPoints K s' * w := by
    rw [hs']; group
  -- Move `T(s)` left past `x_β(b)` and `T(s')` right past `x_{-β}(a)`.
  have hR : D.rootSubgroupPoints β K (ofAdd b) * D.torusPoints K s =
      D.torusPoints K s * D.rootSubgroupPoints β K
        (ofAdd (((torusCharacter s (D.coordinateRoot β))⁻¹ : Kˣ) * b)) := by
    have hc := D.torusPoints_conj_rootSubgroupPoints β K s⁻¹ b
    have hinv : torusCharacter s⁻¹ (D.coordinateRoot β) =
        (torusCharacter s (D.coordinateRoot β))⁻¹ := by
      simp only [torusCharacter_def, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]
    rw [map_inv, inv_inv, hinv] at hc
    rw [← hc]; group
  have hL : D.torusPoints K s' * D.rootSubgroupPoints β' K (ofAdd a) =
      D.rootSubgroupPoints β' K (ofAdd (((torusCharacter s' (D.coordinateRoot β))⁻¹ : Kˣ) * a)) *
        D.torusPoints K s' := by
    have hc := D.torusPoints_conj_rootSubgroupPoints β' K s' a
    rw [D.coordinateRoot_reflectionPerm_self β, torusCharacter_neg] at hc
    rw [← hc]; group
  have heq : D.rootSubgroupPoints β' K (ofAdd a) * D.torusPoints K (h * s) *
      D.rootSubgroupPoints β K (ofAdd (((torusCharacter s (D.coordinateRoot β))⁻¹ : Kˣ) * b)) =
      D.rootSubgroupPoints β' K (ofAdd (((torusCharacter s' (D.coordinateRoot β))⁻¹ : Kˣ) * a)) *
        D.torusPoints K (s' * h) * D.rootSubgroupPoints β K (ofAdd b) := by
    rw [hw] at hcomm
    have h1 : D.rootSubgroupPoints β' K (ofAdd a) * D.torusPoints K h *
        (D.rootSubgroupPoints β K (ofAdd b) * D.torusPoints K s) =
        D.torusPoints K s' * D.rootSubgroupPoints β' K (ofAdd a) * D.torusPoints K h *
          D.rootSubgroupPoints β K (ofAdd b) := by
      simpa only [mul_assoc] using hcomm
    rw [hR, hL] at h1
    simpa only [map_mul, mul_assoc] using h1
  -- Isolate `x_{-β}(...)` on the left and `T(...) * x_β(...) * T(...)` on the right.
  have hsep : D.rootSubgroupPoints β' K
        (ofAdd (a - ((torusCharacter s' (D.coordinateRoot β))⁻¹ : Kˣ) * a)) =
      D.torusPoints K (s' * h) *
        D.rootSubgroupPoints β K
          (ofAdd (b - ((torusCharacter s (D.coordinateRoot β))⁻¹ : Kˣ) * b)) *
        D.torusPoints K (h * s)⁻¹ := by
    let A₁ := D.rootSubgroupPoints β' K (ofAdd a)
    let A₂ := D.rootSubgroupPoints β' K
      (ofAdd (((torusCharacter s' (D.coordinateRoot β))⁻¹ : Kˣ) * a))
    let T₁ := D.torusPoints K (h * s)
    let T₂ := D.torusPoints K (s' * h)
    let B₁ := D.rootSubgroupPoints β K
      (ofAdd (((torusCharacter s (D.coordinateRoot β))⁻¹ : Kˣ) * b))
    let B₂ := D.rootSubgroupPoints β K (ofAdd b)
    have hA : A₂⁻¹ * A₁ = D.rootSubgroupPoints β' K
        (ofAdd (a - ((torusCharacter s' (D.coordinateRoot β))⁻¹ : Kˣ) * a)) := by
      dsimp only [A₁, A₂]
      rw [← map_inv, ← ofAdd_neg, ← map_mul, ← ofAdd_add, neg_add_eq_sub]
    have hB : B₂ * B₁⁻¹ = D.rootSubgroupPoints β K
        (ofAdd (b - ((torusCharacter s (D.coordinateRoot β))⁻¹ : Kˣ) * b)) := by
      dsimp only [B₁, B₂]
      rw [← map_inv, ← ofAdd_neg, ← map_mul, ← ofAdd_add, sub_eq_add_neg]
    have hT : T₁⁻¹ = D.torusPoints K (h * s)⁻¹ := (map_inv _ _).symm
    rw [← hA, ← hB, ← hT]
    calc
      A₂⁻¹ * A₁ = A₂⁻¹ * (A₁ * T₁ * B₁) * (B₁⁻¹ * T₁⁻¹) := by group
      _ = A₂⁻¹ * (A₂ * T₂ * B₂) * (B₁⁻¹ * T₁⁻¹) := by rw [heq]
      _ = T₂ * (B₂ * B₁⁻¹) * T₁⁻¹ := by group
  obtain ⟨hx1, _, ht1⟩ := D.rootSubgroupPoints_eq_one_of_opposite_eq_torus_mul β _ _ _ _ hsep
  have hs'_char : torusCharacter s' (D.coordinateRoot β) = 1 := by
    have ha0 : a - ((torusCharacter s' (D.coordinateRoot β))⁻¹ : Kˣ) * a = 0 := by
      have h0 : ofAdd (a - ((torusCharacter s' (D.coordinateRoot β))⁻¹ : Kˣ) * a) = ofAdd (0 : K) :=
        D.rootSubgroupPoints_injective β' K (by rw [hx1, ofAdd_zero, map_one])
      exact ofAdd.injective h0
    have h1 : (1 - ((torusCharacter s' (D.coordinateRoot β))⁻¹ : Kˣ) : K) * a = 0 := by
      simpa only [sub_mul, one_mul] using ha0
    have hinv1 : ((torusCharacter s' (D.coordinateRoot β))⁻¹ : Kˣ) = 1 :=
      Units.ext (sub_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right ha)).symm
    exact inv_eq_one.mp hinv1
  have hss' : s' = s := by
    have hmul1 : (s' * h) * (h * s)⁻¹ = 1 :=
      D.torusPoints_injective K (ht1.trans (map_one (D.torusPoints K)).symm)
    have hcancel : s' * s⁻¹ = 1 := by
      simpa only [mul_inv_rev, mul_assoc, mul_inv_cancel_left] using
        (by rw [mul_comm h s] at hmul1; exact hmul1 : s' * h * (s * h)⁻¹ = 1)
    exact mul_inv_eq_one.mp hcancel
  exact hs (hss' ▸ hs'_char)

/-! ## Rigidity up to the torus and torus conjugacy -/

/-- The simple coordinate roots of any Chevalley datum are `ℤ`-linearly independent. -/
theorem linearIndependent_coordinateRoot_simpleIndex :
    LinearIndependent ℤ (fun i : Fin t.rank => D.coordinateRoot (t.simpleIndex ht i)) := by
  have hroot : LinearIndependent ℤ
      (fun i : Fin t.rank => (t.simplyConnectedRootDatum ht).root (t.simpleIndex ht i)) := by
    have h := (t.simplyConnectedBase ht).linearIndepOn_root.linearIndependent.comp
      (t.simpleSupportEquivSimplyConnectedBase ht)
      (t.simpleSupportEquivSimplyConnectedBase ht).injective
    simpa only [Function.comp_def, coe_simpleSupportEquivSimplyConnectedBase] using h
  refine LinearIndependent.of_comp D.weightLatticeEmbedding ?_
  simpa only [Function.comp_def, coordinateRoot_def, D.weightLatticeEmbedding_repr,
    Submodule.coe_mk] using hroot

/-- **Rigidity of standard endomorphisms up to the torus.** Over an infinite field with divisible
units (in particular an algebraically closed field), two standard endomorphisms `F` and `F'`
sharing the same injective character map `φ` differ on `D.rootTorusSubgroup K` by conjugation with
a torus point `D.torusPoints K s`. -/
theorem exists_torusPoints_conj_eq_on_rootTorusSubgroup {K : Type v} [Field K] [Infinite K]
    [RootableBy Kˣ ℕ] {F F' : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hF : D.IsStandardEndomorphism K F) (hF' : D.IsStandardEndomorphism K F')
    (hFφ : IsCharacterMap (D.torusPoints K) F φ) (hF'φ : IsCharacterMap (D.torusPoints K) F' φ)
    (hinj : Function.Injective φ) :
    ∃ s : Fin t.rank → Kˣ, ∀ x ∈ D.rootTorusSubgroup K,
      F x = D.torusPoints K s * F' x * (D.torusPoints K s)⁻¹ := by
  obtain ⟨π, c, g, hF_root, hF_char, hπ_neg, hg_neg, hprop⟩ :=
    D.exists_rootPerm_of_isStandardEndomorphism hF hFφ hinj
  obtain ⟨π', c', g', hF'_root, hF'_char, hπ'_neg, hg'_neg, _⟩ :=
    D.exists_rootPerm_of_isStandardEndomorphism hF' hF'φ hinj
  have hπg (α : Fin t.numRoots) : π α = π' α ∧ ∀ u : K, g α u = g' α u := by
    obtain ⟨h1, h2⟩ := D.eq_of_ringHom_torusCharacter_eq hinj
      (g₁ := (g α).toRingHom) (g₂ := (g' α).toRingHom) (hF_char α) (hF'_char α)
    exact ⟨h1, fun u => DFunLike.congr_fun h2 u⟩
  -- The image simple coordinate roots `π(αᵢ)` remain `ℤ`-linearly independent.
  have hlin_π : LinearIndependent ℤ
      (fun i : Fin t.rank => D.coordinateRoot (π (t.simpleIndex ht i))) := by
    choose m n hm hn hmn using fun i : Fin t.rank => hprop (t.simpleIndex ht i)
    rw [Fintype.linearIndependent_iff]
    intro f hf
    have hφf : ∑ i : Fin t.rank, f i • φ (D.coordinateRoot (π (t.simpleIndex ht i))) = 0 := by
      have h := congrArg φ hf
      simpa only [map_sum, map_zsmul, map_zero] using h
    let N : ℤ := ∏ j : Fin t.rank, n j
    have hNf : ∑ i : Fin t.rank,
        (f i * ((∏ j ∈ Finset.univ.erase i, n j) * m i)) •
          D.coordinateRoot (t.simpleIndex ht i) = 0 := by
      have h1 : N • ∑ i : Fin t.rank, f i • φ (D.coordinateRoot (π (t.simpleIndex ht i))) = 0 := by
        rw [hφf, smul_zero]
      rw [Finset.smul_sum] at h1
      refine (Finset.sum_congr rfl fun i _ => ?_).trans h1
      have hN_eq : N = (∏ j ∈ Finset.univ.erase i, n j) * n i := by
        dsimp only [N]
        rw [mul_comm, Finset.mul_prod_erase Finset.univ n (Finset.mem_univ i)]
      calc
        (f i * ((∏ j ∈ Finset.univ.erase i, n j) * m i)) • D.coordinateRoot (t.simpleIndex ht i)
            = (f i * (∏ j ∈ Finset.univ.erase i, n j)) •
                (m i • D.coordinateRoot (t.simpleIndex ht i)) := by rw [← mul_assoc, mul_smul]
        _ = (f i * (∏ j ∈ Finset.univ.erase i, n j)) •
              (n i • φ (D.coordinateRoot (π (t.simpleIndex ht i)))) := by rw [← hmn i]
        _ = N • (f i • φ (D.coordinateRoot (π (t.simpleIndex ht i)))) := by
            rw [← mul_smul, ← mul_smul, hN_eq]
            congr 1
            ring
    have hcoeff := Fintype.linearIndependent_iff.mp D.linearIndependent_coordinateRoot_simpleIndex
      _ hNf
    intro i
    have hprod_ne : (∏ j ∈ Finset.univ.erase i, n j) * m i ≠ 0 :=
      mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun j _ => hn j) (hm i)
    exact (mul_eq_zero.mp (hcoeff i)).resolve_right hprod_ne
  -- Choose a torus point `s` matching `c / c'` on every positive simple root.
  let ψ : (Fin t.rank → ℤ) →ₗ[ℤ] (Fin t.rank → ℤ) :=
    { toFun x := ∑ i : Fin t.rank, x i • D.coordinateRoot (π (t.simpleIndex ht i))
      map_add' x y := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' r x := by
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, mul_smul] }
  have hψ_single (i : Fin t.rank) :
      ψ (Pi.single i 1) = D.coordinateRoot (π (t.simpleIndex ht i)) := by
    dsimp only [ψ, LinearMap.coe_mk, AddHom.coe_mk]
    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, one_smul]
    · intro j _ hji
      simp only [Pi.single_eq_of_ne hji, zero_smul]
    · intro hi
      exact (hi (Finset.mem_univ i)).elim
  have hψ_inj : Function.Injective ψ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    exact funext (Fintype.linearIndependent_iff.mp hlin_π x hx)
  obtain ⟨s, hs⟩ := torusPointMap_surjective_of_injective (R := K) hψ_inj
    (fun i => c (t.simpleIndex ht i) / c' (t.simpleIndex ht i))
  have hs_pos (i : Fin t.rank) :
      torusCharacter s (D.coordinateRoot (π (t.simpleIndex ht i))) =
        c (t.simpleIndex ht i) / c' (t.simpleIndex ht i) := by
    have h := congrFun hs i
    simpa only [torusPointMap_apply, hψ_single] using h
  -- Any standard endomorphism with injective character map satisfies `d(αᵢ) * d(-αᵢ) = 1`.
  have hprod_eq_one : ∀ (G : D.points K →* D.points K), IsCharacterMap (D.torusPoints K) G φ →
      ∀ (σ : Equiv.Perm (Fin t.numRoots)) (d : Fin t.numRoots → Kˣ)
        (e : Fin t.numRoots → (K ≃+* K)),
      (∀ α u, G (D.rootSubgroupPoints α K (ofAdd u)) =
        D.rootSubgroupPoints (σ α) K (ofAdd ((d α : K) * e α u))) →
      (∀ α, σ ((t.simplyConnectedRootDatum ht).reflectionPerm α α) =
        (t.simplyConnectedRootDatum ht).reflectionPerm (σ α) (σ α)) →
      (∀ α, e ((t.simplyConnectedRootDatum ht).reflectionPerm α α) = e α) →
      ∀ i : Fin t.rank,
        d (t.simpleIndex ht i) *
          d ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i)
            (t.simpleIndex ht i)) = 1 := by
    intro G hGφ σ d e hG_root hσ_neg he_neg i
    let α := t.simpleIndex ht i
    let α' := (t.simplyConnectedRootDatum ht).reflectionPerm α α
    let w := D.weylElement α K 1
    have hTrange : (D.torusPoints K).range.map G = (D.torusPoints K).range :=
      hGφ.map_range_eq hinj
    have hw_norm : w ∈ Subgroup.normalizer (D.torusPoints K).range :=
      D.weylElement_mem_normalizer_range_torusPoints i K
    have hGw_norm : G w ∈ Subgroup.normalizer (D.torusPoints K).range := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [← hTrange] at hy ⊢
        obtain ⟨x, hx, rfl⟩ := hy
        refine ⟨w * x * w⁻¹, ((Subgroup.mem_normalizer_iff.mp hw_norm) x).mp hx, ?_⟩
        simp only [map_mul, map_inv]
      · intro hy
        rw [← hTrange] at hy ⊢
        obtain ⟨x, hx, hx_eq⟩ := hy
        have hconj_x : w⁻¹ * x * w ∈ (D.torusPoints K).range := by
          refine ((Subgroup.mem_normalizer_iff.mp hw_norm) (w⁻¹ * x * w)).mpr ?_
          have hcancel : w * (w⁻¹ * x * w) * w⁻¹ = x := by group
          rwa [hcancel]
        refine ⟨w⁻¹ * x * w, hconj_x, ?_⟩
        calc
          G (w⁻¹ * x * w) = (G w)⁻¹ * G x * G w := by simp only [map_mul, map_inv]
          _ = (G w)⁻¹ * (G w * y * (G w)⁻¹) * G w := by rw [hx_eq]
          _ = y := by group
    have hGw_eq : G w =
        D.rootSubgroupPoints (σ α) K (ofAdd (d α : K)) *
          D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm (σ α) (σ α)) K
            (ofAdd (-(d α' : K))) *
          D.rootSubgroupPoints (σ α) K (ofAdd (d α : K)) := by
      simp only [w, weylElement_def, inv_one, Units.val_one, map_mul, hG_root, hσ_neg, he_neg,
        map_one, map_neg, mul_one, mul_neg, α']
    rw [hGw_eq] at hGw_norm
    exact D.mul_eq_one_of_weylProduct_mem_normalizer_range_torusPoints (σ α) (d α) (d α') hGw_norm
  have hc_mul := hprod_eq_one F hFφ π c g hF_root hπ_neg hg_neg
  have hc'_mul := hprod_eq_one F' hF'φ π' c' g' hF'_root hπ'_neg hg'_neg
  -- Agreement on both signs of every simple root subgroup determines agreement on
  -- `D.rootTorusSubgroup K`.
  refine ⟨s, fun x hx => ?_⟩
  let f₁ : D.rootTorusSubgroup K →* D.points K := F.comp (D.rootTorusSubgroup K).subtype
  let f₂ : D.rootTorusSubgroup K →* D.points K :=
    ((MulAut.conj (D.torusPoints K s)).toMonoidHom.comp F').comp (D.rootTorusSubgroup K).subtype
  have hhom : f₁ = f₂ := by
    refine D.rootTorusSubgroup_hom_ext_of_rootable f₁ f₂ (fun i u => ?_) (fun i u => ?_)
    · simp only [f₁, f₂, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      rw [← ofAdd_toAdd u, hF_root, hF'_root, ← (hπg _).1, ← (hπg _).2,
        D.torusPoints_conj_rootSubgroupPoints, hs_pos i]
      congr 2
      simp only [Units.val_div_eq_div_val, ← mul_assoc, div_mul_cancel₀ _ (Units.ne_zero _)]
    · let α := t.simpleIndex ht i
      let α' := (t.simplyConnectedRootDatum ht).reflectionPerm α α
      simp only [f₁, f₂, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      change F (D.rootSubgroupPoints α' K u) =
        D.torusPoints K s * F' (D.rootSubgroupPoints α' K u) * (D.torusPoints K s)⁻¹
      rw [← ofAdd_toAdd u, hF_root, hF'_root, ← (hπg _).1, ← (hπg _).2,
        D.torusPoints_conj_rootSubgroupPoints]
      have hs_neg : torusCharacter s (D.coordinateRoot (π α')) = c α' / c' α' := by
        rw [hπ_neg α, D.coordinateRoot_reflectionPerm_self, torusCharacter_neg, hs_pos i, inv_div]
        have h1 : c α' = (c α)⁻¹ := eq_inv_of_mul_eq_one_right (hc_mul i)
        have h2 : c' α' = (c' α)⁻¹ := eq_inv_of_mul_eq_one_right (hc'_mul i)
        change c' α / c α = c α' / c' α'
        rw [h1, h2, div_inv_eq_mul, div_eq_mul_inv, mul_comm]
      rw [hs_neg]
      congr 2
      simp only [Units.val_div_eq_div_val, ← mul_assoc, div_mul_cancel₀ _ (Units.ne_zero _)]
  simpa only [f₁, f₂, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply] using DFunLike.congr_fun hhom ⟨x, hx⟩

/-- **Torus conjugacy of standard endomorphisms with the same character map.** If `F` and `F'` are
standard endomorphisms with a common injective character map `φ` over an infinite field with
divisible units, and `1 - φ` is injective, then `F` and `F'` are conjugate on
`D.rootTorusSubgroup K` by a torus point `D.torusPoints K u`. -/
theorem exists_torusPoints_conj_comm_on_rootTorusSubgroup {K : Type v} [Field K] [Infinite K]
    [RootableBy Kˣ ℕ] {F F' : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hF : D.IsStandardEndomorphism K F) (hF' : D.IsStandardEndomorphism K F')
    (hFφ : IsCharacterMap (D.torusPoints K) F φ) (hF'φ : IsCharacterMap (D.torusPoints K) F' φ)
    (hinj : Function.Injective φ) (h1φ : Function.Injective ⇑(1 - φ)) :
    ∃ u : Fin t.rank → Kˣ, ∀ x ∈ D.rootTorusSubgroup K,
      F x = D.torusPoints K u * F' ((D.torusPoints K u)⁻¹ * x * D.torusPoints K u) *
        (D.torusPoints K u)⁻¹ := by
  obtain ⟨s, hs⟩ := D.exists_torusPoints_conj_eq_on_rootTorusSubgroup hF hF' hFφ hF'φ hinj
  obtain ⟨u, hu⟩ := hF'φ.exists_eq_mul_inv h1φ s
  refine ⟨u, fun x hx => ?_⟩
  rw [hs x hx, hu, map_mul, map_mul, map_inv]
  group

/-- **Lang's equation on the actual torus of a Chevalley datum.** Over a commutative ring of
characteristic `p` with divisible units, if an endomorphism `F` has character map `φ` satisfying
`φ ^ n = (p ^ r) • 1` with `r > 0`, then every torus point `D.torusPoints K s` equals
`D.torusPoints K u * (F (D.torusPoints K u))⁻¹` for some `u`. -/
theorem exists_torusPoints_eq_mul_inv_of_pow_eq_nsmul_one {K : Type v} [CommRing K]
    [RootableBy Kˣ ℕ] (p : ℕ) [CharP K p] {F : D.points K →* D.points K}
    {φ : Module.End ℤ (Fin t.rank → ℤ)} (hφ : IsCharacterMap (D.torusPoints K) F φ)
    {n r : ℕ} (hr : 0 < r) (hpow : φ ^ n = (p ^ r : ℕ) • 1) (s : Fin t.rank → Kˣ) :
    ∃ u, D.torusPoints K s = D.torusPoints K u * (F (D.torusPoints K u))⁻¹ := by
  obtain hK | _ := subsingleton_or_nontrivial K
  · exact ⟨s, Subsingleton.elim _ _⟩
  have hpr : ((p ^ r : ℕ) : ℤ) ≠ 1 := by
    rw [Nat.cast_ne_one, Ne, pow_eq_one_iff, not_or]
    exact ⟨CharP.char_ne_one K p, hr.ne'⟩
  exact hφ.exists_eq_mul_inv
    (injective_one_sub_of_pow_eq_smul_one (by rwa [Nat.cast_smul_eq_nsmul]) hpr) s

/-- **Torus conjugacy when a power of the character map is a nonzero scalar other than `1`.**
Covers both Frobenius-type Steinberg character maps (`m = q > 1`) and negative scalings
(`m = -q`). Injectivity of `φ` and of `1 - φ` both follow from `φ ^ n = m • 1` with `m ≠ 0, 1`. -/
theorem exists_torusPoints_conj_comm_on_rootTorusSubgroup_of_pow_eq_smul_one {K : Type v}
    [Field K] [Infinite K] [RootableBy Kˣ ℕ] {F F' : D.points K →* D.points K}
    {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hF : D.IsStandardEndomorphism K F) (hF' : D.IsStandardEndomorphism K F')
    (hFφ : IsCharacterMap (D.torusPoints K) F φ) (hF'φ : IsCharacterMap (D.torusPoints K) F' φ)
    {n : ℕ} {m : ℤ} (hm0 : m ≠ 0) (hm1 : m ≠ 1) (hpow : φ ^ n = m • 1) :
    ∃ u : Fin t.rank → Kˣ, ∀ x ∈ D.rootTorusSubgroup K,
      F x = D.torusPoints K u * F' ((D.torusPoints K u)⁻¹ * x * D.torusPoints K u) *
        (D.torusPoints K u)⁻¹ := by
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    cases n with
    | zero =>
      have hmx : x = m • x := by
        have h := LinearMap.congr_fun hpow x
        simpa [pow_zero] using h
      have hsub : (m - 1) • x = 0 := by rw [sub_smul, one_smul, ← hmx, sub_self]
      exact (smul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hm1)
    | succ k =>
      have hmx : m • x = 0 := by
        have h := LinearMap.congr_fun hpow x
        simp only [pow_succ, mul_apply_eq_comp, hx, map_zero, LinearMap.smul_apply,
          one_apply_eq_self] at h
        exact h.symm
      exact (smul_eq_zero.mp hmx).resolve_left hm0
  exact D.exists_torusPoints_conj_comm_on_rootTorusSubgroup hF hF' hFφ hF'φ hinj
    (injective_one_sub_of_pow_eq_smul_one hpow hm1)

/-- **Torus conjugacy in positive characteristic `p` when `φ ^ n = (p ^ r) • 1` with `r > 0`.**
Applies directly to Frobenius-type and twisted Steinberg endomorphisms over algebraically closed
fields of prime characteristic. -/
theorem exists_torusPoints_conj_comm_on_rootTorusSubgroup_of_charP {K : Type v}
    [Field K] [Infinite K] [RootableBy Kˣ ℕ] (p : ℕ) [CharP K p] (hp : p ≠ 0)
    {F F' : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hF : D.IsStandardEndomorphism K F) (hF' : D.IsStandardEndomorphism K F')
    (hFφ : IsCharacterMap (D.torusPoints K) F φ) (hF'φ : IsCharacterMap (D.torusPoints K) F' φ)
    {n r : ℕ} (hr : 0 < r) (hpow : φ ^ n = (p ^ r : ℕ) • 1) :
    ∃ u : Fin t.rank → Kˣ, ∀ x ∈ D.rootTorusSubgroup K,
      F x = D.torusPoints K u * F' ((D.torusPoints K u)⁻¹ * x * D.torusPoints K u) *
        (D.torusPoints K u)⁻¹ := by
  have hpr0 : ((p ^ r : ℕ) : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (pow_ne_zero r hp)
  have hpr1 : ((p ^ r : ℕ) : ℤ) ≠ 1 := by
    rw [Nat.cast_ne_one, Ne, pow_eq_one_iff, not_or]
    exact ⟨CharP.char_ne_one K p, hr.ne'⟩
  exact D.exists_torusPoints_conj_comm_on_rootTorusSubgroup_of_pow_eq_smul_one
    hF hF' hFφ hF'φ hpr0 hpr1 (by rwa [Nat.cast_smul_eq_nsmul])

end TauCeti.DynkinType.ChevalleyDatum
