/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Torus.Weyl
import TauCeti.Algebra.AlgebraicGroup.Chevalley.RankOne
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Root.Weyl
import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# Strong-exchange shortening for lifted Weyl words of Chevalley data

For a Chevalley datum `D` of any valid Dynkin type `t` (including `G₂`) over an arbitrary
commutative ring `A`, conjugating Steinberg's Weyl element `n_γ(s)` by `n_{αᵢ}(1)` produces
`n_{sᵢ γ}(ε s)` (`ChevalleyDatum.weylElement_conj_weylElement`), so conjugating by a word of
pinned simple Weyl representatives transports `n_γ(s)` to `n_{w γ}(s')`.

Adapting the strong-exchange word-deletion and identity inductions of
`TauCeti.exists_wordProd_eraseIdx_eq_mul_ofIdx` and `TauCeti.eq_one_of_inversions_eq_empty` from
`TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange` to lifted words in `D.points A`
shows that any word of pinned simple Weyl representatives spelling `1` in the Weyl group lies in
the actual character-lattice torus `T_D(A)`
(`ChevalleyDatum.weylWord_mem_range_torusPoints_of_geckWeylWordProd_eq_one`).

## Main results

* `TauCeti.DynkinType.ChevalleyDatum.weylWord_mem_range_torusPoints_of_geckWeylWordProd_eq_one`:
  any word of pinned simple Weyl representatives spelling `1` in the Weyl group lies in
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
          ((t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht l) γ) A s' := by
  induction l generalizing γ s with
  | nil => exact ⟨s, by simp⟩
  | cons i l ih =>
    obtain ⟨s₁, hs₁⟩ := ih γ s
    refine ⟨Units.map (Int.castRingHom A).toMonoidHom
      (t.chevalleyWeylSign ht (t.simpleIndex ht i)
        ((t.simplyConnectedRootDatum ht).weylGroupToPerm
          (t.geckWeylWordProd ht l) γ)) * s₁, ?_⟩
    rw [List.map_cons, List.prod_cons, mul_inv_rev, geckWeylWordProd_cons,
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

/-- Head-deletion step for `exists_eraseIdx_weylWord_mul_weylElement` when the first inversion
occurs at the leading letter `j`. -/
private theorem exists_eraseIdx_weylWord_mul_weylElement_head (A : Type v) [CommRing A]
    {γ : Fin t.numRoots} (j : Fin t.rank) (l : List (Fin t.rank))
    (hpos : (t.simplyConnectedBase ht).IsPos
      ((t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht l) γ))
    (hneg : ¬(t.simplyConnectedBase ht).IsPos
      ((t.simplyConnectedRootDatum ht).reflectionPerm (t.simpleIndex ht j)
        ((t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht l) γ))) :
    t.geckWeylWordProd ht l =
        t.geckWeylWordProd ht (j :: l) *
          RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ ∧
      ∃ r : Fin t.rank → Aˣ,
        ((j :: l).map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod *
            D.weylElement γ A 1 =
          D.torusPoints A r *
            (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  let P := t.simplyConnectedRootDatum ht
  let b := t.simplyConnectedBase ht
  have hkey : P.weylGroupToPerm (t.geckWeylWordProd ht l) γ = t.simpleIndex ht j := by
    by_contra hne
    have hmem : P.weylGroupToPerm (t.geckWeylWordProd ht l) γ ∈
        posRoots P b \ {t.simpleIndex ht j} :=
      ⟨(mem_posRoots P b _).mpr hpos, hne⟩
    have hjmem : t.simpleIndex ht j ∈ b.support := by
      rw [← support_rationalBase]
      exact simpleIndex_mem_support j
    exact hneg ((mem_posRoots P b _).mp
      ((reflectionPerm_mem_posRoots_diff_singleton_iff P b hjmem _).mpr hmem).1)
  refine ⟨?_, ?_⟩
  · rw [geckWeylWordProd_cons, ← hkey, RootPairing.weylGroup.ofIdx_weylGroupToPerm_eq_conj,
      inv_mul_cancel_right, mul_assoc, RootPairing.weylGroup.ofIdx_mul_self, mul_one]
  · obtain ⟨s', hs'⟩ := D.exists_unit_weylWord_conj_weylElement A l γ 1
    rw [hkey, D.weylElement_eq_corootPoints_mul (t.simpleIndex ht j) A s',
      ← D.simpleCorootPoints_eq_corootPoints, D.simpleCorootPoints_eq_torusPoints] at hs'
    have hW :
        (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod * D.weylElement γ A 1 =
          D.torusPoints A (D.simpleCorootParameter j A s') *
            D.weylElement (t.simpleIndex ht j) A 1 *
            (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod :=
      mul_inv_eq_iff_eq_mul.mp hs'
    refine ⟨D.simpleReflectionTorusParameter j A (D.simpleCorootParameter j A s') *
        D.simpleCorootParameter j A (-1), ?_⟩
    rw [List.map_cons, List.prod_cons, mul_assoc, hW, map_mul,
      ← D.simpleCorootPoints_eq_torusPoints j A (-1), ← D.weylElement_mul_self,
      ← D.weylElement_conj_torusPoints]
    group

/-- **Strong-exchange shortening of Weyl words in `D.points A`.** If `l` spells a Weyl element
sending a positive root `γ` to a negative root, multiplying the lifted word on the right by
`n_γ(1)` deletes a letter from `l` up to a left factor in the actual torus `T_D(A)`. -/
private theorem exists_eraseIdx_weylWord_mul_weylElement (A : Type v) [CommRing A]
    {γ : Fin t.numRoots} (hγ : (t.simplyConnectedBase ht).IsPos γ) (l : List (Fin t.rank))
    (h : ¬(t.simplyConnectedBase ht).IsPos
      ((t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht l) γ)) :
    ∃ p < l.length,
      t.geckWeylWordProd ht (l.eraseIdx p) =
        t.geckWeylWordProd ht l *
          RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ ∧
      ∃ r : Fin t.rank → Aˣ,
        (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod * D.weylElement γ A 1 =
          D.torusPoints A r *
            ((l.eraseIdx p).map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod := by
  induction l with
  | nil => exact absurd (by simpa using hγ) h
  | cons j l ih =>
    rw [geckWeylWordProd_cons, RootPairing.weylGroupToPerm_ofIdx_mul_apply] at h
    by_cases hpos : (t.simplyConnectedBase ht).IsPos
        ((t.simplyConnectedRootDatum ht).weylGroupToPerm (t.geckWeylWordProd ht l) γ)
    · obtain ⟨hw, r, hr⟩ := D.exists_eraseIdx_weylWord_mul_weylElement_head A j l hpos h
      exact ⟨0, by simp, hw, r, hr⟩
    · obtain ⟨p, hp, hw, r, hr⟩ := ih hpos
      refine ⟨p + 1, by simpa using hp, ?_, D.simpleReflectionTorusParameter j A r, ?_⟩
      · rw [List.eraseIdx_cons_succ, geckWeylWordProd_cons, hw, geckWeylWordProd_cons, mul_assoc]
      · rw [List.eraseIdx_cons_succ, List.map_cons, List.prod_cons, List.map_cons, List.prod_cons,
          mul_assoc, hr, ← D.weylElement_conj_torusPoints]
        group

/-- **Any word of simple Weyl representatives spelling `1` in the Weyl group lies in the actual
torus `T_D(A)`**, over an arbitrary commutative ring `A` and for every valid Dynkin type. -/
theorem weylWord_mem_range_torusPoints_of_geckWeylWordProd_eq_one (A : Type v) [CommRing A]
    (l : List (Fin t.rank)) (hl : t.geckWeylWordProd ht l = 1) :
    (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod ∈ (D.torusPoints A).range := by
  let _ := t.isReduced_simplyConnectedRootDatum ht
  let P := t.simplyConnectedRootDatum ht
  let b := t.simplyConnectedBase ht
  suffices ∀ n (l' : List (Fin t.rank)), l'.length = n → t.geckWeylWordProd ht l' = 1 →
      (l'.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod ∈ (D.torusPoints A).range from
    this l.length l rfl hl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro l' hlen hl'
    rcases List.eq_nil_or_concat l' with rfl | ⟨l₁, k, rfl⟩
    · exact ⟨1, by simp⟩
    · rw [List.concat_eq_append, geckWeylWordProd_append, geckWeylWordProd_cons,
        geckWeylWordProd_nil, mul_one] at hl'
      have hl₁ :
          t.geckWeylWordProd ht l₁ = RootPairing.weylGroup.ofIdx P (t.simpleIndex ht k) := by
        calc
          t.geckWeylWordProd ht l₁
              = t.geckWeylWordProd ht l₁ *
                  (RootPairing.weylGroup.ofIdx P (t.simpleIndex ht k) *
                    RootPairing.weylGroup.ofIdx P (t.simpleIndex ht k)) := by
                rw [RootPairing.weylGroup.ofIdx_mul_self, mul_one]
          _ = (t.geckWeylWordProd ht l₁ * RootPairing.weylGroup.ofIdx P (t.simpleIndex ht k)) *
                RootPairing.weylGroup.ofIdx P (t.simpleIndex ht k) := (mul_assoc _ _ _).symm
          _ = RootPairing.weylGroup.ofIdx P (t.simpleIndex ht k) := by rw [hl', one_mul]
      have hkpos : b.IsPos (t.simpleIndex ht k) := by
        rw [← mem_posRoots, ← posRoots_rationalRootSystem]
        exact simpleIndex_mem_posRoots k
      have hkneg :
          ¬b.IsPos (P.weylGroupToPerm (t.geckWeylWordProd ht l₁) (t.simpleIndex ht k)) := by
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
