/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Weyl
import TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange

/-!
# Strong-exchange shortening for lifted Weyl words of Chevalley data

For a Chevalley datum `D` of any valid Dynkin type `t` (including `G₂`) over an arbitrary
commutative ring `A`, conjugating Steinberg's Weyl element `n_γ(s)` by `n_{αᵢ}(1)` produces
`n_{sᵢ γ}(ε s)` (`ChevalleyDatum.weylElement_conj_weylElement`), so conjugating by a word of
pinned simple Weyl representatives transports `n_γ(s)` to `n_{w γ}(s')`.

Transporting the strong-exchange witness
(`RootPairing.exists_wordProd_drop_apply_eq_and_wordProd_eraseIdx_eq_mul_ofIdx`) from
`TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange` to lifted words in `D.points A`
and tracking the resulting torus correction shows that any word of pinned simple Weyl
representatives spelling `1` in the Weyl group lies in the actual character-lattice torus `T_D(A)`
(`ChevalleyDatum.weylWord_mem_range_torusPoints_of_simplyConnectedWeylWordProd_eq_one`).

## Main results

* `ChevalleyDatum.weylWord_mem_range_torusPoints_of_simplyConnectedWeylWordProd_eq_one`: any
  word of pinned simple Weyl representatives spelling `1` in the Weyl group lies in
  `(D.torusPoints A).range`, over every commutative ring `A` and for every valid Dynkin type.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19–22.
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, Ch. III, §10.3.
* R. W. Carter, *Simple Groups of Lie Type*, §7.2.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

universe v

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)

private theorem exists_unit_weylWord_conj_weylElement (A : Type v) [CommRing A]
    (l : List (Fin t.rank)) (γ : Fin t.numRoots) (s : Aˣ) :
    ∃ s' : Aˣ,
      (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod * D.weylElement γ A s *
          ((l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod)⁻¹ =
        D.weylElement
          ((t.simplyConnectedRootDatum ht).weylGroupToPerm (t.simplyConnectedWeylWordProd ht l) γ)
          A s' := by
  induction l generalizing γ s with
  | nil => exact ⟨s, by simp⟩
  | cons i l ih =>
    obtain ⟨s₁, hs₁⟩ := ih γ s
    refine ⟨Units.map (Int.castRingHom A).toMonoidHom
      (t.chevalleyWeylSign ht (t.simpleIndex ht i)
        ((t.simplyConnectedRootDatum ht).weylGroupToPerm
          (t.simplyConnectedWeylWordProd ht l) γ)) * s₁, ?_⟩
    rw [List.map_cons, List.prod_cons, mul_inv_rev, simplyConnectedWeylWordProd_cons,
      RootPairing.weylGroupToPerm_ofIdx_mul_apply]
    calc
      D.weylElement (t.simpleIndex ht i) A 1 *
            (l.map fun j => D.weylElement (t.simpleIndex ht j) A 1).prod *
            D.weylElement γ A s *
            (((l.map fun j => D.weylElement (t.simpleIndex ht j) A 1).prod)⁻¹ *
              (D.weylElement (t.simpleIndex ht i) A 1)⁻¹)
          = D.weylElement (t.simpleIndex ht i) A 1 *
              ((l.map fun j => D.weylElement (t.simpleIndex ht j) A 1).prod *
                D.weylElement γ A s *
                ((l.map fun j => D.weylElement (t.simpleIndex ht j) A 1).prod)⁻¹) *
              (D.weylElement (t.simpleIndex ht i) A 1)⁻¹ := by group
      _ = _ := by rw [hs₁, D.weylElement_conj_weylElement]

private theorem exists_torusPoints_mul_list_prod (A : Type v) [CommRing A]
    (l : List (Fin t.rank)) (r : Fin t.rank → Aˣ) :
    ∃ r' : Fin t.rank → Aˣ,
      (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod * D.torusPoints A r =
        D.torusPoints A r' *
          (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod := by
  have hnorm := D.weylSubgroup_le_normalizer_range_torusPoints A
    (D.list_prod_map_weylElement_mem_weylSubgroup A l)
  obtain ⟨r', hr'⟩ := (Subgroup.mem_normalizer_iff.mp hnorm (D.torusPoints A r)).mp ⟨r, rfl⟩
  exact ⟨r', by rw [hr']; group⟩

/-- Rank-one torus cancellation across a crossing suffix: given the suffix conjugation identity
`suf_lift * n_γ(1) * suf_lift⁻¹ = n_{αᵢ}(s')`, cancelling `nᵢ(1)` against `n_{αᵢ}(s')` produces
a left factor in the actual torus `T_D(A)`. -/
private theorem exists_weylElement_mul_list_prod_mul_eq_torusPoints_mul
    (A : Type v) [CommRing A] (i : Fin t.rank) (suf : List (Fin t.rank)) {γ : Fin t.numRoots}
    {s' : Aˣ}
    (hsuf : (suf.map fun j => D.weylElement (t.simpleIndex ht j) A 1).prod *
        D.weylElement γ A 1 *
        ((suf.map fun j => D.weylElement (t.simpleIndex ht j) A 1).prod)⁻¹ =
      D.weylElement (t.simpleIndex ht i) A s') :
    ∃ r₀ : Fin t.rank → Aˣ,
      D.weylElement (t.simpleIndex ht i) A 1 *
          (suf.map fun j => D.weylElement (t.simpleIndex ht j) A 1).prod *
          D.weylElement γ A 1 =
        D.torusPoints A r₀ *
          (suf.map fun j => D.weylElement (t.simpleIndex ht j) A 1).prod := by
  rw [D.weylElement_simpleIndex_eq_torusPoints_mul] at hsuf
  have hW := mul_inv_eq_iff_eq_mul.mp hsuf
  refine ⟨D.simpleReflectionTorusParameter i A (D.simpleCorootParameter i A s') *
    D.simpleCorootParameter i A (-1), ?_⟩
  rw [mul_assoc, hW, map_mul, ← D.simpleCorootPoints_eq_torusPoints i A (-1),
    ← D.weylElement_mul_self, ← D.weylElement_conj_torusPoints]
  group

/-- **Strong-exchange shortening of Weyl words in `D.points A`.** If `l` spells a Weyl element
sending a positive root `γ` to a negative root, multiplying the lifted word on the right by
`n_γ(1)` deletes a letter from `l` up to a left factor in the actual torus `T_D(A)`. -/
private theorem exists_eraseIdx_weylWord_mul_weylElement (A : Type v) [CommRing A]
    {γ : Fin t.numRoots} (hγ : (t.simplyConnectedBase ht).IsPos γ) (l : List (Fin t.rank))
    (h : ¬(t.simplyConnectedBase ht).IsPos
      ((t.simplyConnectedRootDatum ht).weylGroupToPerm (t.simplyConnectedWeylWordProd ht l) γ)) :
    ∃ p < l.length,
      t.simplyConnectedWeylWordProd ht (l.eraseIdx p) =
        t.simplyConnectedWeylWordProd ht l *
          RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ ∧
      ∃ r : Fin t.rank → Aˣ,
        (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod * D.weylElement γ A 1 =
          D.torusPoints A r *
            ((l.eraseIdx p).map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  let e := t.simpleSupportEquivSimplyConnectedBase ht
  rw [← t.wordProd_map_simpleSupportEquiv ht] at h
  obtain ⟨p, hp, hdrop, hwp⟩ :=
    (t.simplyConnectedRootDatum ht).exists_wordProd_drop_apply_eq_and_wordProd_eraseIdx_eq_mul_ofIdx
      (t.simplyConnectedBase ht) hγ (l.map e) h
  have hp' : p < l.length := by simpa using hp
  have hdrop' :
      (t.simplyConnectedRootDatum ht).weylGroupToPerm
          (t.simplyConnectedWeylWordProd ht (l.drop (p + 1))) γ =
        t.simpleIndex ht l[p] := by
    simpa [e, ← List.map_drop] using hdrop
  have hwp' :
      t.simplyConnectedWeylWordProd ht (l.eraseIdx p) =
        t.simplyConnectedWeylWordProd ht l *
          RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ := by
    simpa [e, List.eraseIdx_map] using hwp
  obtain ⟨s', hs'⟩ := D.exists_unit_weylWord_conj_weylElement A (l.drop (p + 1)) γ 1
  rw [hdrop'] at hs'
  obtain ⟨r₀, hmid⟩ :=
    D.exists_weylElement_mul_list_prod_mul_eq_torusPoints_mul A l[p] (l.drop (p + 1)) hs'
  obtain ⟨r, hr⟩ := D.exists_torusPoints_mul_list_prod A (l.take p) r₀
  refine ⟨p, hp', hwp', r, ?_⟩
  have hl_split : l.take p ++ l[p] :: l.drop (p + 1) = l := by
    rw [← List.drop_eq_getElem_cons hp', List.take_append_drop]
  calc
    (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod * D.weylElement γ A 1
        = ((l.take p).map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod *
            (D.weylElement (t.simpleIndex ht l[p]) A 1 *
              ((l.drop (p + 1)).map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod *
              D.weylElement γ A 1) := by
          conv_lhs => rw [← hl_split]
          simp only [List.map_append, List.map_cons, List.prod_append, List.prod_cons, mul_assoc]
    _ = ((l.take p).map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod *
            D.torusPoints A r₀ *
            ((l.drop (p + 1)).map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod := by
          rw [hmid, mul_assoc]
    _ = D.torusPoints A r *
            ((l.eraseIdx p).map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod := by
          rw [hr, List.eraseIdx_eq_take_drop_succ, List.map_append, List.prod_append, mul_assoc]

/-- **Any word of simple Weyl representatives spelling `1` in the Weyl group lies in the actual
torus `T_D(A)`**, over an arbitrary commutative ring `A` and for every valid Dynkin type. -/
theorem weylWord_mem_range_torusPoints_of_simplyConnectedWeylWordProd_eq_one (A : Type v)
    [CommRing A] (l : List (Fin t.rank)) (hl : t.simplyConnectedWeylWordProd ht l = 1) :
    (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod ∈ (D.torusPoints A).range := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  let P := t.simplyConnectedRootDatum ht
  let b := t.simplyConnectedBase ht
  suffices ∀ n (l' : List (Fin t.rank)), l'.length = n → t.simplyConnectedWeylWordProd ht l' = 1 →
      (l'.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod ∈ (D.torusPoints A).range from
    this l.length l rfl hl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l' hlen hl'
    rcases List.eq_nil_or_concat l' with rfl | ⟨l₁, k, rfl⟩
    · exact ⟨1, by simp⟩
    · rw [List.concat_eq_append, simplyConnectedWeylWordProd_append,
        simplyConnectedWeylWordProd_cons, simplyConnectedWeylWordProd_nil, mul_one] at hl'
      have hl₁ :
          t.simplyConnectedWeylWordProd ht l₁ =
            RootPairing.weylGroup.ofIdx P (t.simpleIndex ht k) :=
        (eq_inv_of_mul_eq_one_left hl').trans (RootPairing.weylGroup.ofIdx_inv_eq P _)
      have hkpos : b.IsPos (t.simpleIndex ht k) := by
        rw [← mem_posRoots, ← posRoots_rationalRootSystem]
        exact simpleIndex_mem_posRoots k
      have hkneg :
          ¬b.IsPos
            (P.weylGroupToPerm (t.simplyConnectedWeylWordProd ht l₁) (t.simpleIndex ht k)) := by
        rw [hl₁, RootPairing.weylGroupToPerm_ofIdx_apply, ← mem_posRoots]
        exact reflectionPerm_self_notMem_posRoots P b ((mem_posRoots P b _).mpr hkpos)
      obtain ⟨p, hp, hwp, r, hr⟩ :=
        D.exists_eraseIdx_weylWord_mul_weylElement A hkpos l₁ hkneg
      have hlen_lt : (l₁.eraseIdx p).length < n := by
        have hlen' := List.length_eraseIdx_add_one hp
        rw [← hlen, List.concat_eq_append, List.length_append]
        omega
      obtain ⟨s, hs⟩ := ih _ hlen_lt (l₁.eraseIdx p) rfl (hwp.trans hl')
      rw [List.concat_eq_append, List.map_append, List.prod_append, List.map_singleton,
        List.prod_singleton, hr, ← hs, ← map_mul]
      exact ⟨r * s, rfl⟩

end TauCeti.DynkinType.ChevalleyDatum
