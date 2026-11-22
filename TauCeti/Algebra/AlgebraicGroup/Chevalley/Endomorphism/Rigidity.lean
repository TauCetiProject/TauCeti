/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.RootAction
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Gauss
import TauCeti.Algebra.AlgebraicGroup.Chevalley.HomExt

/-!
# Rigidity and torus conjugacy of standard endomorphisms

Over an infinite field `K` with divisible units (in particular an algebraically closed field),
two standard endomorphisms `F` and `F'` of the points of a Chevalley datum `D` that share the
same injective character map `φ` agree on `D.rootTorusSubgroup K` up to left-composition with
conjugation by a torus point, i.e., `F = Int(s) ∘ F'` on `D.rootTorusSubgroup K`
(`ChevalleyDatum.exists_torusPoints_conj_eq_on_rootTorusSubgroup`).

The proof combines three ingredients:
* the root permutation and field automorphisms on root subgroups extracted from `φ` in
  `TauCeti.Algebra.AlgebraicGroup.Chevalley.Endomorphism.RootAction`, together with linear
  independence of the simple coordinate roots
  (`ChevalleyDatum.linearIndependent_coordinateRoot_simpleIndex`), which provides a torus point `s`
  matching the scalar ratios on the positive simple roots;
* the rank-one normalizer lemma over any infinite field
  (`ChevalleyDatum.mul_eq_one_of_rootSubgroupPoints_mul_opposite_mul_mem_normalizer`), forcing the
  product of opposite simple root scalars to be `1`;
* determination of homomorphisms on `D.rootTorusSubgroup K` by the positive and negative simple
  root subgroups (`ChevalleyDatum.rootTorusSubgroup_hom_ext_of_rootable`).

When in addition `1 - φ` is injective, Lang's equation on the torus
(`TauCeti.IsCharacterMap.exists_eq_mul_inv`) promotes left-composition by `Int(s)` to actual
conjugacy `F = Int(u) ∘ F' ∘ Int(u)⁻¹` on `D.rootTorusSubgroup K`
(`ChevalleyDatum.exists_torusPoints_conjugate_on_rootTorusSubgroup`), specializing to endomorphisms
with `φ ^ n = m • 1` (`m ≠ 0, 1`), and in particular to `φ ^ n = (p ^ r) • 1` (`r > 0`) in positive
characteristic `p`.

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.exists_torusPoints_conj_eq_on_rootTorusSubgroup`: rigidity up
  to left-composition with conjugation by a torus point (`F = Int(s) ∘ F'` on
  `D.rootTorusSubgroup K`) for standard endomorphisms with a common injective character map.
* `TauCeti.DynkinType.ChevalleyDatum.exists_torusPoints_conjugate_on_rootTorusSubgroup`: conjugacy
  `F = Int(u) ∘ F' ∘ Int(u)⁻¹` on `D.rootTorusSubgroup K` by a torus point when `1 - φ` is
  injective.
* `TauCeti.DynkinType.ChevalleyDatum.exists_torusPoints_eq_mul_inv_of_pow_eq_nsmul_one`: Lang's
  equation on `D.torusPoints` when `φ ^ n = (p ^ r) • 1` with `r > 0` in characteristic `p`.
* `ChevalleyDatum.exists_torusPoints_conjugate_on_rootTorusSubgroup_of_pow_eq_smul_one` and
  `ChevalleyDatum.exists_torusPoints_conjugate_on_rootTorusSubgroup_of_charP`:
  torus conjugacy when a power of `φ` is a nonzero scalar other than `1`, in particular a positive
  power of a prime characteristic.

## References

* R. Steinberg, *Endomorphisms of linear algebraic groups*, Mem. Amer. Math. Soc. **80** (1968),
  Theorem 10.1 and §11.
* R. Steinberg, *Lectures on Chevalley Groups*, Chapters 3 and 10.
* R. W. Carter, *Finite Groups of Lie Type: Conjugacy Classes and Complex Characters*, §1.17.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

open Multiplicative

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

/-! ## Rigidity up to the torus and torus conjugacy -/

private theorem linearIndependent_of_smul_eq_smul {ι R M : Type*} [CommRing R] [IsDomain R]
    [AddCommGroup M] [Module R M] {b v : ι → M} {m n : ι → R}
    (hb : LinearIndependent R b) (hm : ∀ i, m i ≠ 0) (hn : ∀ i, n i ≠ 0)
    (hmn : ∀ i, n i • v i = m i • b i) : LinearIndependent R v := by
  classical
  rw [linearIndependent_iff'] at hb ⊢
  intro s f hf i hi
  let N : R := ∏ j ∈ s, n j
  have hscaled : ∑ j ∈ s, (f j * (∏ k ∈ s.erase j, n k) * m j) • b j = 0 := by
    have h0 : ∑ j ∈ s, N • (f j • v j) = 0 := by rw [← Finset.smul_sum, hf, smul_zero]
    refine (Finset.sum_congr rfl fun j hj => ?_).trans h0
    have hN : N = (∏ k ∈ s.erase j, n k) * n j := by
      dsimp only [N]
      rw [mul_comm, Finset.mul_prod_erase s n hj]
    calc
      (f j * (∏ k ∈ s.erase j, n k) * m j) • b j
          = (f j * ∏ k ∈ s.erase j, n k) • (m j • b j) := by rw [mul_smul]
      _ = (f j * ∏ k ∈ s.erase j, n k) • (n j • v j) := by rw [hmn j]
      _ = ((∏ k ∈ s.erase j, n k) * n j * f j) • v j := by
        rw [← mul_smul]
        congr 1
        ring
      _ = N • (f j • v j) := by rw [← hN, mul_smul]
  have hc := hb s _ hscaled i hi
  have hprod : (∏ k ∈ s.erase i, n k) * m i ≠ 0 :=
    mul_ne_zero (Finset.prod_ne_zero_iff.mpr fun k _ => hn k) (hm i)
  rw [mul_assoc] at hc
  exact (mul_eq_zero.mp hc).resolve_right hprod

private theorem opposite_simple_scalar_mul_eq_one {K : Type v} [Field K] [Infinite K]
    [RootableBy Kˣ ℕ] {G : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hGφ : IsCharacterMap (D.torusPoints K) G φ) (hinj : Function.Injective φ)
    {σ : Equiv.Perm (Fin t.numRoots)} {d : Fin t.numRoots → Kˣ}
    {e : Fin t.numRoots → (K ≃+* K)}
    (hG_root : ∀ α u, G (D.rootSubgroupPoints α K (ofAdd u)) =
      D.rootSubgroupPoints (σ α) K (ofAdd ((d α : K) * e α u)))
    (hσ_neg : ∀ α, σ ((t.simplyConnectedRootDatum ht).reflectionPerm α α) =
      (t.simplyConnectedRootDatum ht).reflectionPerm (σ α) (σ α))
    (i : Fin t.rank) :
    d (t.simpleIndex ht i) *
      d ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht i)
        (t.simpleIndex ht i)) = 1 := by
  let α := t.simpleIndex ht i
  let α' := (t.simplyConnectedRootDatum ht).reflectionPerm α α
  let w := D.weylElement α K 1
  have hTrange : (D.torusPoints K).range.map G = (D.torusPoints K).range :=
    hGφ.map_range_eq hinj
  have hGw_norm : G w ∈ Subgroup.normalizer (D.torusPoints K).range := by
    rw [← hTrange]
    exact Subgroup.le_normalizer_map G
      ⟨w, D.weylElement_mem_normalizer_range_torusPoints i K, rfl⟩
  have hGw_eq : G w = D.rootSubgroupPoints (σ α) K (ofAdd (d α : K)) *
      D.rootSubgroupPoints ((t.simplyConnectedRootDatum ht).reflectionPerm (σ α) (σ α)) K
        (ofAdd (-(d α' : K))) *
      D.rootSubgroupPoints (σ α) K (ofAdd (d α : K)) := by
    simp only [w, weylElement_def, inv_one, Units.val_one, map_mul, hG_root, hσ_neg,
      map_one, map_neg, mul_one, mul_neg, α']
  exact Units.ext <| by
    simpa only [Units.val_mul, Units.val_one] using
      D.mul_eq_one_of_rootSubgroupPoints_mul_opposite_mul_mem_normalizer (σ α) (d α : K)
        (d α') (hGw_eq ▸ hGw_norm)

/-- **Rigidity of standard endomorphisms up to the torus.** Over an infinite field with divisible
units (in particular an algebraically closed field), two standard endomorphisms `F` and `F'`
sharing the same injective character map `φ` satisfy `F = Int(s) ∘ F'` on `D.rootTorusSubgroup K`
for some torus point `D.torusPoints K s`. -/
theorem exists_torusPoints_conj_eq_on_rootTorusSubgroup {K : Type v} [Field K] [Infinite K]
    [RootableBy Kˣ ℕ] {F F' : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hF : D.IsStandardEndomorphism K F) (hF' : D.IsStandardEndomorphism K F')
    (hFφ : IsCharacterMap (D.torusPoints K) F φ) (hF'φ : IsCharacterMap (D.torusPoints K) F' φ)
    (hinj : Function.Injective φ) :
    ∃ s : Fin t.rank → Kˣ, ∀ x ∈ D.rootTorusSubgroup K,
      F x = D.torusPoints K s * F' x * (D.torusPoints K s)⁻¹ := by
  obtain ⟨π, c, g, hF_root, hF_char, hπ_neg, _, hprop⟩ :=
    D.exists_rootPerm_of_isStandardEndomorphism hF hFφ hinj
  obtain ⟨π', c', g', hF'_root, hF'_char, hπ'_neg, _, _⟩ :=
    D.exists_rootPerm_of_isStandardEndomorphism hF' hF'φ hinj
  have hπg (α : Fin t.numRoots) : π α = π' α ∧ ∀ u : K, g α u = g' α u := by
    obtain ⟨h1, h2⟩ := D.eq_of_ringHom_torusCharacter_eq hinj
      (g₁ := (g α).toRingHom) (g₂ := (g' α).toRingHom) (hF_char α) (hF'_char α)
    exact ⟨h1, fun u => DFunLike.congr_fun h2 u⟩
  have hlin_π : LinearIndependent ℤ
      (fun i : Fin t.rank => D.coordinateRoot (π (t.simpleIndex ht i))) := by
    choose m n hm hn hmn using fun i : Fin t.rank => hprop (t.simpleIndex ht i)
    exact (linearIndependent_of_smul_eq_smul D.linearIndependent_coordinateRoot_simpleIndex
      hm hn hmn).of_comp φ
  let ψ := Fintype.linearCombination ℤ
    (fun i : Fin t.rank => D.coordinateRoot (π (t.simpleIndex ht i)))
  have hψ_single (i : Fin t.rank) :
      ψ (Pi.single i 1) = D.coordinateRoot (π (t.simpleIndex ht i)) := by
    simp [ψ, Fintype.linearCombination_apply_single]
  have hψ_inj : Function.Injective ψ := hlin_π.fintypeLinearCombination_injective
  obtain ⟨s, hs⟩ := torusPointMap_surjective_of_injective (R := K) hψ_inj
    (fun i => c (t.simpleIndex ht i) / c' (t.simpleIndex ht i))
  have hs_pos (i : Fin t.rank) :
      torusCharacter s (D.coordinateRoot (π (t.simpleIndex ht i))) =
        c (t.simpleIndex ht i) / c' (t.simpleIndex ht i) := by
    simpa only [torusPointMap_apply, hψ_single] using congrFun hs i
  have hc_mul := D.opposite_simple_scalar_mul_eq_one hFφ hinj hF_root hπ_neg
  have hc'_mul := D.opposite_simple_scalar_mul_eq_one hF'φ hinj hF'_root hπ'_neg
  have hroot (α : Fin t.numRoots)
      (hs_α : torusCharacter s (D.coordinateRoot (π α)) = c α / c' α)
      (u : Multiplicative K) :
      F (D.rootSubgroupPoints α K u) =
        D.torusPoints K s * F' (D.rootSubgroupPoints α K u) * (D.torusPoints K s)⁻¹ := by
    rw [← ofAdd_toAdd u, hF_root, hF'_root, ← (hπg _).1, ← (hπg _).2,
      D.torusPoints_conj_rootSubgroupPoints, hs_α]
    congr 2
    simp only [Units.val_div_eq_div_val, ← mul_assoc, div_mul_cancel₀ _ (Units.ne_zero _)]
  refine ⟨s, fun x hx => ?_⟩
  let f₁ : D.rootTorusSubgroup K →* D.points K := F.comp (D.rootTorusSubgroup K).subtype
  let f₂ : D.rootTorusSubgroup K →* D.points K :=
    ((MulAut.conj (D.torusPoints K s)).toMonoidHom.comp F').comp (D.rootTorusSubgroup K).subtype
  have hhom : f₁ = f₂ := D.rootTorusSubgroup_hom_ext_of_rootable f₁ f₂
    (fun i u => by
      simp only [f₁, f₂, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      exact hroot (t.simpleIndex ht i) (hs_pos i) u)
    (fun i u => by
      let α := t.simpleIndex ht i
      let α' := (t.simplyConnectedRootDatum ht).reflectionPerm α α
      simp only [f₁, f₂, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      refine hroot α' ?_ u
      have h1 : c α' = (c α)⁻¹ := eq_inv_of_mul_eq_one_right (hc_mul i)
      have h2 : c' α' = (c' α)⁻¹ := eq_inv_of_mul_eq_one_right (hc'_mul i)
      rw [hπ_neg α, D.coordinateRoot_reflectionPerm_self, torusCharacter_neg, hs_pos i, inv_div,
        h1, h2, div_inv_eq_mul, div_eq_mul_inv, mul_comm])
  simpa only [f₁, f₂, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply] using DFunLike.congr_fun hhom ⟨x, hx⟩

/-- **Torus conjugacy of standard endomorphisms with the same character map.** If `F` and `F'` are
standard endomorphisms with a common injective character map `φ` over an infinite field with
divisible units, and `1 - φ` is injective, then `F` and `F'` are conjugate on
`D.rootTorusSubgroup K` by a torus point `D.torusPoints K u`. -/
theorem exists_torusPoints_conjugate_on_rootTorusSubgroup {K : Type v} [Field K] [Infinite K]
    [RootableBy Kˣ ℕ] {F F' : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hF : D.IsStandardEndomorphism K F) (hF' : D.IsStandardEndomorphism K F')
    (hFφ : IsCharacterMap (D.torusPoints K) F φ) (hF'φ : IsCharacterMap (D.torusPoints K) F' φ)
    (hinj : Function.Injective φ) (h1φ : Function.Injective ⇑(1 - φ)) :
    ∃ u : Fin t.rank → Kˣ, ∀ x ∈ D.rootTorusSubgroup K,
      F x = D.torusPoints K u * F' ((D.torusPoints K u)⁻¹ * x * D.torusPoints K u) *
        (D.torusPoints K u)⁻¹ := by
  obtain ⟨s, hs⟩ := D.exists_torusPoints_conj_eq_on_rootTorusSubgroup hF hF' hFφ hF'φ hinj
  obtain ⟨u, hu⟩ := hF'φ.exists_eq_mul_inv h1φ s
  exact ⟨u, fun x hx => by rw [hs x hx, hu, map_mul, map_mul, map_inv]; group⟩

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
    rw [Nat.cast_ne_one, Ne, pow_eq_one_iff, not_or]; exact ⟨CharP.char_ne_one K p, hr.ne'⟩
  exact hφ.exists_eq_mul_inv_of_pow_eq_smul_one hpr (by rwa [Nat.cast_smul_eq_nsmul]) s

/-- **Torus conjugacy when a power of the character map is a nonzero scalar other than `1`.**
Covers both Frobenius-type Steinberg character maps (`m = q > 1`) and negative scalings
(`m = -q`). Injectivity of `φ` and of `1 - φ` both follow from `φ ^ n = m • 1` with `m ≠ 0, 1`. -/
theorem exists_torusPoints_conjugate_on_rootTorusSubgroup_of_pow_eq_smul_one {K : Type v}
    [Field K] [Infinite K] [RootableBy Kˣ ℕ] {F F' : D.points K →* D.points K}
    {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hF : D.IsStandardEndomorphism K F) (hF' : D.IsStandardEndomorphism K F')
    (hFφ : IsCharacterMap (D.torusPoints K) F φ) (hF'φ : IsCharacterMap (D.torusPoints K) F' φ)
    {n : ℕ} {m : ℤ} (hm0 : m ≠ 0) (hm1 : m ≠ 1) (hpow : φ ^ n = m • 1) :
    ∃ u : Fin t.rank → Kˣ, ∀ x ∈ D.rootTorusSubgroup K,
      F x = D.torusPoints K u * F' ((D.torusPoints K u)⁻¹ * x * D.torusPoints K u) *
        (D.torusPoints K u)⁻¹ := by
  have hinj : Function.Injective φ := (injective_iff_map_eq_zero φ).mpr fun x hx => by
    cases n with
    | zero =>
      have hmx : x = m • x := by simpa [pow_zero] using LinearMap.congr_fun hpow x
      have hsub : (m - 1) • x = 0 := by rw [sub_smul, one_smul, ← hmx, sub_self]
      exact (smul_eq_zero.mp hsub).resolve_left (sub_ne_zero.mpr hm1)
    | succ k =>
      have hmx : m • x = 0 := by
        simpa only [pow_succ, mul_apply_eq_comp, hx, map_zero, LinearMap.smul_apply,
          one_apply_eq_self] using (LinearMap.congr_fun hpow x).symm
      exact (smul_eq_zero.mp hmx).resolve_left hm0
  exact D.exists_torusPoints_conjugate_on_rootTorusSubgroup hF hF' hFφ hF'φ hinj
    (injective_one_sub_of_pow_eq_smul_one hpow hm1)

/-- **Torus conjugacy in positive characteristic `p` when `φ ^ n = (p ^ r) • 1` with `r > 0`.**
Applies directly to Frobenius-type and twisted Steinberg endomorphisms over algebraically closed
fields of prime characteristic. -/
theorem exists_torusPoints_conjugate_on_rootTorusSubgroup_of_charP {K : Type v}
    [Field K] [Infinite K] [RootableBy Kˣ ℕ] (p : ℕ) [CharP K p] (hp : p ≠ 0)
    {F F' : D.points K →* D.points K} {φ : Module.End ℤ (Fin t.rank → ℤ)}
    (hF : D.IsStandardEndomorphism K F) (hF' : D.IsStandardEndomorphism K F')
    (hFφ : IsCharacterMap (D.torusPoints K) F φ) (hF'φ : IsCharacterMap (D.torusPoints K) F' φ)
    {n r : ℕ} (hr : 0 < r) (hpow : φ ^ n = (p ^ r : ℕ) • 1) :
    ∃ u : Fin t.rank → Kˣ, ∀ x ∈ D.rootTorusSubgroup K,
      F x = D.torusPoints K u * F' ((D.torusPoints K u)⁻¹ * x * D.torusPoints K u) *
        (D.torusPoints K u)⁻¹ :=
  D.exists_torusPoints_conjugate_on_rootTorusSubgroup_of_pow_eq_smul_one
    hF hF' hFφ hF'φ (Nat.cast_ne_zero.mpr (pow_ne_zero r hp))
    (by rw [Nat.cast_ne_one, Ne, pow_eq_one_iff, not_or]; exact ⟨CharP.char_ne_one K p, hr.ne'⟩)
    (by rwa [Nat.cast_smul_eq_nsmul])

end TauCeti.DynkinType.ChevalleyDatum
