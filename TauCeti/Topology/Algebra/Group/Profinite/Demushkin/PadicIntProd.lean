/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.NormalForm.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.Abelianization
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.FinitePresentation
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.CohomFp
import TauCeti.Data.ZMod.TrivialAction

/-!
# `ℤ_p × ℤ_p` is a Demushkin group

The additive group `ℤ_p × ℤ_p`, realized as `Multiplicative (Fin 2 → ℤ_[p])`, is the pro-`p`
group `⟨x₁, x₂ ∣ (x₁, x₂)⟩` with the single surface relation `(x₁, x₂) = x₁⁻¹ x₂⁻¹ x₁ x₂`. It is
the first infinite example of a Demushkin group, of rank two and with torsion-free abelianization
(Labute, p. 106; Serre, *Galois Cohomology*, I §4.5). The three clauses of the predicate are proved
as follows.

* `d(ℤ_p × ℤ_p) = 2`, so `H¹(ℤ_p × ℤ_p, 𝔽_p)` is two-dimensional: this is the case `#X = 2` of
  `d(ℤ_p^X) = #X` (`TauCeti.topologicalGeneratorRankNat_multiplicative_pi_padicInt` in
  `TauCeti.Topology.Algebra.Group.Profinite.ProP.PadicInt.CohomFp`).
* `H²(ℤ_p × ℤ_p, 𝔽_p)` is one-dimensional. The upper bound is the relation-rank bound for the
  one-relator presentation `⟨x₁, x₂ ∣ (x₁, x₂)⟩`, whose presented group is identified with
  `ℤ_p × ℤ_p` by the exponent-sum map (`TauCeti.presentedProPEquivPiPadicInt`): its kernel is the
  closed commutator subgroup, which is the closed normal closure of the relator because the
  commutator of the two free generators dies in the presented group
  (`Subgroup.topologicalClosure_commutator_le_of_forall_commutatorElement_mem`). The lower bound
  is the nonvanishing of the cup product of the two coordinate characters `e_1^*`, `e_2^*`
  (`TauCeti.cupFp_piPadicIntCoordinateCharacter_ne_zero`).
* The cup pairing is nondegenerate. Every class of `H¹` is the class of a continuous character
  `χ : ℤ_p × ℤ_p → 𝔽_p`, and if `χ` is nonzero it is nonzero on some coordinate vector `e_i`. The
  symmetry test `TauCeti.mul_eq_mul_of_cupFp_eq_zero` then shows that `χ` pairs nontrivially with
  the other coordinate character `e_j^*`: a vanishing cup product would force
  `χ(e_i) e_j^*(e_j) = χ(e_j) e_j^*(e_i)`, that is `χ(e_i) = 0`.

The relator is written as the `q = 0` normal-form word `TauCeti.demushkinWordNeTwo 0 2` of the
classification, so that this example is the rank-two, `q = 0` normal form itself.

## Main definitions

* `TauCeti.presentedProPEquivPiPadicInt`: the identification `⟨x₁, x₂ ∣ (x₁, x₂)⟩ ≃ₜ* ℤ_p × ℤ_p`.

## Main results

* `TauCeti.topologicalClosure_normalClosure_demushkinWordNeTwo_zero_two`: the closed normal
  closure of `(x₁, x₂)` in the free pro-`p` group on two generators is its closed commutator
  subgroup.
* `TauCeti.finrank_cohomFp_two_multiplicative_pi_padicInt_fin_two`: `H²(ℤ_p × ℤ_p, 𝔽_p)` is
  one-dimensional.
* `TauCeti.isDemushkin_multiplicative_pi_padicInt_fin_two`: **`ℤ_p × ℤ_p` is a Demushkin group**,
  of rank two (`TauCeti.demushkinRank_multiplicative_pi_padicInt_fin_two`).

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, p. 106.
* J.-P. Serre, *Galois Cohomology*, Springer (1997), Chapter I, §4.5.
* J. Neukirch, A. Schmidt, K. Wingberg, *Cohomology of Number Fields*, 2nd ed., Springer (2008),
  Chapter III, §9.
-/

public section

namespace TauCeti

open ContCohomology Multiplicative Subgroup

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the explicit
-- `H2 G (ZMod p)` below is the one the relation-rank theory is stated for, as in
-- `TauCeti.Topology.Algebra.Group.Profinite.ProP.ElementaryAbelian`.
attribute [local instance 2000] Ring.toAddCommGroup

variable (p : ℕ) [Fact p.Prime]

/-! ### The presentation `⟨x₁, x₂ ∣ (x₁, x₂)⟩` -/

section Presentation

omit [Fact p.Prime] in
/-- In `⟨x₁, x₂ ∣ (x₁, x₂)⟩` the two generators commute: the relator is their commutator. -/
private theorem presentedProP.commute_of_zero_of_one :
    Commute (presentedProP.of p {demushkinWordNeTwo 0 2 (freeProPGen p 2)} 0)
      (presentedProP.of p {demushkinWordNeTwo 0 2 (freeProPGen p 2)} 1) := by
  rw [← labuteComm_eq_one_iff_commute, ← presentedProP.mk_of, ← presentedProP.mk_of,
    ← map_labuteComm]
  exact presentedProP.mk_relator _ (by
    rw [Set.mem_singleton_iff, demushkinWordNeTwo_zero_two, freeProPGen_of_lt p zero_lt_two,
      freeProPGen_of_lt p one_lt_two, Fin.mk_zero, Fin.mk_one])

/-- **The closed normal closure of `(x₁, x₂)` is the kernel of the exponent-sum map** of the free
pro-`p` group on two generators, that is its closed commutator subgroup. -/
theorem topologicalClosure_normalClosure_demushkinWordNeTwo_zero_two :
    (normalClosure ({demushkinWordNeTwo 0 2 (freeProPGen p 2)} :
        Set (freeProP p (Fin 2)))).topologicalClosure =
      (freeProP.exponentSum p (Fin 2) :
        freeProP p (Fin 2) →* Multiplicative (Fin 2 → ℤ_[p])).ker := by
  apply le_antisymm
  · -- The relator dies in the commutative group `ℤ_p × ℤ_p`, and the kernel is closed.
    refine topologicalClosure_minimal _ (normalClosure_le_normal ?_)
      (isClosed_singleton.preimage (freeProP.exponentSum p (Fin 2)).continuous)
    rw [Set.singleton_subset_iff, SetLike.mem_coe, MonoidHom.mem_ker, MonoidHom.coe_ofClass,
      demushkinWordNeTwo_zero_two, freeProPGen_of_lt p zero_lt_two, freeProPGen_of_lt p one_lt_two,
      Fin.mk_zero, Fin.mk_one, map_labuteComm, labuteComm_eq_one]
  · -- The kernel is the closed commutator subgroup, and the commutators of the two generators die
    -- in the presented group, where the generators commute.
    intro y hy
    rw [MonoidHom.mem_ker, MonoidHom.coe_ofClass, freeProP.exponentSum_eq_one_iff] at hy
    refine topologicalClosure_commutator_le_of_forall_commutatorElement_mem
      (freeProP.topologicalClosure_closure_range_of_eq_top p (Fin 2))
      (isClosed_topologicalClosure _) ?_ hy
    rintro _ ⟨i, rfl⟩ _ ⟨j, rfl⟩
    rw [← presentedProP.mk_eq_one_iff, map_commutatorElement, commutatorElement_eq_one_iff_commute,
      presentedProP.mk_of, presentedProP.mk_of]
    fin_cases i <;> fin_cases j
    · exact Commute.refl _
    · exact presentedProP.commute_of_zero_of_one p
    · exact (presentedProP.commute_of_zero_of_one p).symm
    · exact Commute.refl _

/-- **`⟨x₁, x₂ ∣ (x₁, x₂)⟩ ≃ₜ* ℤ_p × ℤ_p`**, the exponent-sum isomorphism: the generator `xᵢ` goes
to the coordinate vector `eᵢ` (`TauCeti.presentedProPEquivPiPadicInt_of`). -/
noncomputable def presentedProPEquivPiPadicInt :
    presentedProP p (Fin 2) {demushkinWordNeTwo 0 2 (freeProPGen p 2)} ≃ₜ*
      Multiplicative (Fin 2 → ℤ_[p]) :=
  (presentedProP.congrOfClosureEq (by
    rw [topologicalClosure_normalClosure_demushkinWordNeTwo_zero_two,
      (freeProP.exponentSum p (Fin 2)).topologicalClosure_normalClosure_ker])).trans
    (presentedProP.equivOfSurjective (freeProP.exponentSum p (Fin 2))
      (freeProP.exponentSum_surjective p (Fin 2)))

/-- The exponent-sum isomorphism sends the class of a word to its exponent vector. -/
@[simp]
theorem presentedProPEquivPiPadicInt_mk (y : freeProP p (Fin 2)) :
    presentedProPEquivPiPadicInt p (presentedProP.mk p _ y) = freeProP.exponentSum p (Fin 2) y := by
  rw [presentedProPEquivPiPadicInt, ContinuousMulEquiv.trans_apply,
    presentedProP.congrOfClosureEq_mk, presentedProP.equivOfSurjective_mk]

/-- The exponent-sum isomorphism sends the generator `xᵢ` to the coordinate vector `eᵢ`. -/
@[simp]
theorem presentedProPEquivPiPadicInt_of (i : Fin 2) :
    presentedProPEquivPiPadicInt p (presentedProP.of p _ i) = ofAdd (Pi.single i (1 : ℤ_[p])) := by
  rw [← presentedProP.mk_of, presentedProPEquivPiPadicInt_mk, freeProP.exponentSum_of]

end Presentation

/-! ### `ℤ_p × ℤ_p` is Demushkin -/

/-- **`H²(ℤ_p × ℤ_p, 𝔽_p)` is one-dimensional.** At most one-dimensional, because `ℤ_p × ℤ_p` has
the one-relator presentation `⟨x₁, x₂ ∣ (x₁, x₂)⟩`; at least one-dimensional, because the cup
product of the two coordinate characters is nonzero. -/
theorem finrank_cohomFp_two_multiplicative_pi_padicInt_fin_two :
    Module.finrank (ZMod p) (cohomFp p (Multiplicative (Fin 2 → ℤ_[p])) 2) = 1 := by
  set G := Multiplicative (Fin 2 → ℤ_[p])
  -- The explicit `H²(G, 𝔽_p)` needs an action of `G` on `𝔽_p`; the trivial one is installed for
  -- the duration of the proof and does not appear in the statement.
  let _ := trivialZModAction p G
  have htriv : ∀ (g : G) (m : ZMod p), g • m = m := fun _ _ ↦ rfl
  have : ContinuousSMul G (ZMod p) := ⟨continuous_snd⟩
  set r := demushkinWordNeTwo 0 2 (freeProPGen p 2)
  have hrels : ({r} : Set (freeProP p (Fin 2))) ⊆ proPFrattini p (freeProP p (Fin 2)) :=
    Set.singleton_subset_iff.mpr (demushkinWordNeTwo_mem_proPFrattini Fact.out (dvd_zero p) 2 _)
  have hfin : Finite (H2 G (ZMod p)) :=
    (presentedProP.finite_H2_iff_exists_finite_relation_system {r} hrels
      (presentedProPEquivPiPadicInt p) htriv).mpr ⟨{r}, by rw [Finset.coe_singleton]⟩
  have hfg := (presentedProP.finite_H2_iff {r} hrels (presentedProPEquivPiPadicInt p) htriv).mp hfin
  -- One relator bounds the relation rank by one.
  have hle : Module.finrank (ZMod p) (H2 G (ZMod p)) ≤ 1 :=
    (presentedProP.finrank_H2_le_iff {r} hrels (presentedProPEquivPiPadicInt p) htriv hfg 1).mpr
      ⟨{⟨r, le_topologicalClosure _ (subset_normalClosure rfl)⟩}, by simp,
        by rw [Finset.coe_singleton, Set.image_singleton]⟩
  have : Finite (H2 G (ZMod p)) := hfin
  have : Module.Finite (ZMod p) (H2 G (ZMod p)) := Module.Finite.of_finite
  have : Module.Finite (ZMod p) (cohomFp p G 2) :=
    Module.Finite.equiv (cohomFpLinearEquivH2 p G htriv).symm
  -- The cup product of the two coordinate characters is a nonzero class.
  exact le_antisymm ((cohomFpLinearEquivH2 p G htriv).finrank_eq.trans_le hle)
    (Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨_, cupFp_piPadicIntCoordinateCharacter_ne_zero p (Fin 2) Fin.zero_ne_one⟩)

/-- **`ℤ_p × ℤ_p` is a Demushkin group** at every prime `p`: it is pro-`p`, `H¹(ℤ_p × ℤ_p, 𝔽_p)` is
two-dimensional, `H²(ℤ_p × ℤ_p, 𝔽_p)` is one-dimensional, and the cup pairing is nondegenerate:
a nonzero class is the class of a character `χ` which is nonzero on a coordinate vector `e_i`, and
`χ` pairs nontrivially with the coordinate character `e_j^*` for `j ≠ i`, by the symmetry test
`TauCeti.mul_eq_mul_of_cupFp_eq_zero` on the commuting elements `e_i`, `e_j`. -/
theorem isDemushkin_multiplicative_pi_padicInt_fin_two :
    IsDemushkin p (Multiplicative (Fin 2 → ℤ_[p])) := by
  set G := Multiplicative (Fin 2 → ℤ_[p])
  have hP : IsProP p G := isProP_multiplicative_pi_padicInt p (Fin 2)
  -- A nonzero character is nonzero on some coordinate vector.
  have key : ∀ χ : continuousZModDual p G, χ ≠ 0 →
      ∃ i : Fin 2, toAdd (Additive.toMul χ (ofAdd (Pi.single i (1 : ℤ_[p])))) ≠ 0 := fun χ hχ ↦
    not_forall_not.mp fun hall ↦ hχ
      (continuousZModDual_eq_zero_of_forall_ofAdd_single p (Fin 2) fun i ↦ not_not.mp (hall i))
  refine
    { isProP := hP
      finite_cohomFp_one :=
        hP.finite_cohomFp_one_iff.2
          (isTopologicallyFinitelyGenerated_multiplicative_pi_padicInt p _)
      finrank_cohomFp_two := finrank_cohomFp_two_multiplicative_pi_padicInt_fin_two p
      cup_separatingLeft := fun a ha ↦ ?_
      cup_separatingRight := fun b hb ↦ ?_ }
  · obtain ⟨i, hi⟩ := key (cohomFpLinearEquivContinuousZModDual p G a)
      ((cohomFpLinearEquivContinuousZModDual p G).map_ne_zero_iff.2 ha)
    obtain ⟨j, hj⟩ := exists_ne i
    refine ⟨(cohomFpLinearEquivContinuousZModDual p G).symm
      (piPadicIntCoordinateCharacter p (Fin 2) j), fun h ↦ hi ?_⟩
    have := mul_eq_mul_of_cupFp_eq_zero p h
      (Commute.all (ofAdd (Pi.single i (1 : ℤ_[p]))) (ofAdd (Pi.single j 1)))
    rwa [LinearEquiv.apply_symm_apply, piPadicIntCoordinateCharacter_ofAdd_single_self,
      piPadicIntCoordinateCharacter_ofAdd_single_of_ne p (Fin 2) hj, mul_one, mul_zero] at this
  · obtain ⟨i, hi⟩ := key (cohomFpLinearEquivContinuousZModDual p G b)
      ((cohomFpLinearEquivContinuousZModDual p G).map_ne_zero_iff.2 hb)
    obtain ⟨j, hj⟩ := exists_ne i
    refine ⟨(cohomFpLinearEquivContinuousZModDual p G).symm
      (piPadicIntCoordinateCharacter p (Fin 2) j), fun h ↦ hi ?_⟩
    have := mul_eq_mul_of_cupFp_eq_zero p h
      (Commute.all (ofAdd (Pi.single j (1 : ℤ_[p]))) (ofAdd (Pi.single i 1)))
    rwa [LinearEquiv.apply_symm_apply, piPadicIntCoordinateCharacter_ofAdd_single_self,
      piPadicIntCoordinateCharacter_ofAdd_single_of_ne p (Fin 2) hj, one_mul, zero_mul] at this

/-- **`ℤ_p × ℤ_p` is a Demushkin group of rank two.** -/
@[simp]
theorem demushkinRank_multiplicative_pi_padicInt_fin_two :
    demushkinRank (isDemushkin_multiplicative_pi_padicInt_fin_two p) = 2 := by
  rw [demushkinRank_def, topologicalGeneratorRankNat_multiplicative_pi_padicInt,
    Nat.card_eq_fintype_card, Fintype.card_fin]

end TauCeti
