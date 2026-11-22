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

Transporting the strong-exchange witness (`TauCeti.exists_wordProd_eraseIdx_eq_mul_ofIdx_and_drop`)
from `TauCeti.LinearAlgebra.RootSystem.Inversions.StrongExchange` to lifted words in `D.points A`
and tracking the resulting torus correction shows that any word of pinned simple Weyl
representatives spelling `1` in the Weyl group lies in the actual character-lattice torus `T_D(A)`
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

private theorem exists_torusPoints_mul_list_prod (A : Type v) [CommRing A]
    (l : List (Fin t.rank)) (r : Fin t.rank → Aˣ) :
    ∃ r' : Fin t.rank → Aˣ,
      (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod * D.torusPoints A r =
        D.torusPoints A r' *
          (l.map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod := by
  induction l generalizing r with
  | nil => exact ⟨r, by simp⟩
  | cons i l ih =>
    obtain ⟨r₁, hr₁⟩ := ih r
    refine ⟨D.simpleReflectionTorusParameter i A r₁, ?_⟩
    rw [List.map_cons, List.prod_cons, mul_assoc, hr₁, ← mul_assoc,
      ← D.weylElement_conj_torusPoints]
    group

private theorem wordProd_map_simpleSupportEquiv (l : List (Fin t.rank)) :
    TauCeti.wordProd (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht)
        (l.map (t.simpleSupportEquivSimplyConnectedBase ht)) =
      t.geckWeylWordProd ht l := by
  induction l with
  | nil => rw [List.map_nil, wordProd_nil, geckWeylWordProd_nil]
  | cons i l ih =>
    rw [List.map_cons, wordProd_cons, ih, geckWeylWordProd_cons,
      coe_simpleSupportEquivSimplyConnectedBase_apply]

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
  let _ := t.isReduced_simplyConnectedRootDatum ht
  let e := t.simpleSupportEquivSimplyConnectedBase ht
  rw [← wordProd_map_simpleSupportEquiv] at h
  obtain ⟨p, hp, hdrop, hwp⟩ := TauCeti.exists_wordProd_eraseIdx_eq_mul_ofIdx_and_drop
    (t.simplyConnectedRootDatum ht) (t.simplyConnectedBase ht) hγ (l.map e) h
  have hp' : p < l.length := by simpa using hp
  have hdrop' :
      (t.simplyConnectedRootDatum ht).weylGroupToPerm
          (t.geckWeylWordProd ht (l.drop (p + 1))) γ =
        t.simpleIndex ht l[p] := by
    simpa [e, ← List.map_drop, wordProd_map_simpleSupportEquiv] using hdrop
  have hwp' :
      t.geckWeylWordProd ht (l.eraseIdx p) =
        t.geckWeylWordProd ht l *
          RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ := by
    simpa [e, List.eraseIdx_map, wordProd_map_simpleSupportEquiv] using hwp
  obtain ⟨s', hs'⟩ := D.exists_unit_weylWord_conj_weylElement A (l.drop (p + 1)) γ 1
  rw [hdrop', D.weylElement_simpleIndex_eq_torusPoints_mul] at hs'
  have hW :
      ((l.drop (p + 1)).map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod *
          D.weylElement γ A 1 =
        D.torusPoints A (D.simpleCorootParameter l[p] A s') *
          D.weylElement (t.simpleIndex ht l[p]) A 1 *
          ((l.drop (p + 1)).map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod :=
    mul_inv_eq_iff_eq_mul.mp hs'
  let r₀ : Fin t.rank → Aˣ :=
    D.simpleReflectionTorusParameter l[p] A (D.simpleCorootParameter l[p] A s') *
      D.simpleCorootParameter l[p] A (-1)
  have hmid :
      D.weylElement (t.simpleIndex ht l[p]) A 1 *
          ((l.drop (p + 1)).map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod *
          D.weylElement γ A 1 =
        D.torusPoints A r₀ *
          ((l.drop (p + 1)).map fun i => D.weylElement (t.simpleIndex ht i) A 1).prod := by
    rw [mul_assoc, hW]
    dsimp only [r₀]
    rw [map_mul, ← D.simpleCorootPoints_eq_torusPoints l[p] A (-1), ← D.weylElement_mul_self,
      ← D.weylElement_conj_torusPoints]
    group
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
