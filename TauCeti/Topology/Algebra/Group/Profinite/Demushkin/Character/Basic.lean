/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.AdicCompletion.Newton
public import TauCeti.Topology.Algebra.Group.Profinite.Demushkin.Criterion
public import TauCeti.Topology.Algebra.Group.Profinite.Free.CrossedHomLinearization
public import TauCeti.Topology.Algebra.Group.Profinite.Free.PadicUnits
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription.Equiv
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Prescription.Presentation
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.NumberTheory.Padics.Matrix
import TauCeti.Topology.Algebra.Group.Profinite.ProP.CrossedHom

/-!
# The canonical character of a Demushkin group

A Demushkin group `G` has exactly one continuous character `χ : G → ℤ_pˣ` with Labute's prescription
property (`TauCeti.HasPrescriptionProperty`): every reduction `H¹(G, I(χ)/pⁱ) → H¹(G, I(χ)/p)` of
the twisted coefficients is surjective (Labute, Theorem 4). This file proves that theorem and
defines the character, `TauCeti.demushkinCharacter`, the *canonical character* or *orientation*
of `G`, whose image is the second invariant of the classification of Demushkin groups.

Write `G = ⟨x₁, …, x_n ∣ r⟩` with `r ∈ Φ(F)` in the free pro-`p` group `F`. A continuous character
`χ` of `G` is determined by its values `u_i = χ(x_i)`, which are principal units `1 + pℤ_p`, and by
the relator criterion
(`TauCeti.presentedProP.hasPrescriptionProperty_iff_forall_isCrossedHom_eq_zero`) it has the
prescription property exactly when every continuous crossed homomorphism `F → ℤ_p` for the induced
character of `F` vanishes at `r`. The existence and uniqueness theorem holds for every
one-relator pro-`p` group whose relator has nondegenerate degree-one form
(`TauCeti.freeProP.degreeOneForm`), a condition every Demushkin group satisfies
(`TauCeti.IsDemushkin.nondegenerate_degreeOneForm`); it needs no normal form of the relator and is
uniform in `p`.

## Main definitions

* `TauCeti.demushkinCharacter`: the canonical character of a Demushkin group.

## Main results

* `TauCeti.existsUnique_hasPrescriptionProperty_presentedProP_of_nondegenerate`: a one-relator
  pro-`p` group whose relator has nondegenerate degree-one form has exactly one continuous
  character with the prescription property.
* `TauCeti.IsDemushkin.existsUnique_hasPrescriptionProperty`: Labute's Theorem 4, existence and
  uniqueness of the canonical character of a Demushkin group.
* `TauCeti.hasPrescriptionProperty_demushkinCharacter`,
  `TauCeti.HasPrescriptionProperty.eq_demushkinCharacter`,
  `TauCeti.hasPrescriptionProperty_iff_eq_demushkinCharacter`: the canonical character has the
  prescription property, and it is the only character that does.
* `TauCeti.demushkinCharacter_of_equiv`, `TauCeti.range_demushkinCharacter_of_equiv`: the
  canonical character, and its image, are invariant under topological isomorphism, across
  universes.
* `TauCeti.range_demushkinCharacter_eq_of_equiv`: the image of the canonical character of `G` is
  `A` as soon as `G` is isomorphic to a group all of whose characters with the prescription property
  have image `A`; this reads the image table of the normal forms on the canonical character.
* `TauCeti.isClosed_range_demushkinCharacter`: the image of the canonical character is a closed
  subgroup of `ℤ_pˣ`, contained in the principal units
  (`TauCeti.demushkinCharacter_apply_mem_unitsPrincipal_one`).

## References

* J. P. Labute, *Classification of Demushkin groups*, Canad. J. Math. 19 (1967), 106–132, §2,
  Proposition 6 and Theorem 4.
* J.-P. Serre, *Structure de certains pro-p-groupes*, Séminaire Bourbaki 252 (1962/63).
-/

public section

namespace TauCeti

open freeProP Matrix

universe u v w

-- Preferring the ring path keeps a single additive structure on `ZMod p`, so that the trivial
-- action installed below is the one the cocycles and the degree-one form are stated against.
attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [Fact p.Prime] {X : Type u}

/-- **Newton's method for the relator.** Under a nondegenerate degree-one form, there is exactly
one continuous character of the free pro-`p` group, trivial modulo `p` on the generators, whose
Kronecker crossed homomorphisms all vanish at the relator. -/
private theorem existsUnique_character_forall_crossedHom_single_eq_zero [Finite X] [DecidableEq X]
    {r : freeProP p X}
    (hr : r ∈ proPFrattini p (freeProP p X))
    (hnd : (degreeOneForm (gradedMk p (freeProP p X) 1
      ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩)).Nondegenerate) :
    ∃! χ : freeProP p X →ₜ* ℤ_[p]ˣ, (∀ i, (p : ℤ_[p]) ∣ (χ (of i) : ℤ_[p]) - 1) ∧
      ∀ j, crossedHom χ (Pi.single j 1) r = 0 := by
  classical
  have := Fintype.ofFinite X
  set n : pLowerCentralSeries p (freeProP p X) 1 :=
    ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩
  -- The matrix of the degree-one form in the dual basis of the generators, lifted to `ℤ_p` and
  -- transposed; its determinant is a unit because the form is nondegenerate.
  set M : Matrix X X ℤ_[p] := ((LinearMap.BilinForm.toMatrix (dualBasis p X)
    (degreeOneForm (gradedMk p (freeProP p X) 1 n))).map (ZMod.cast : ZMod p → ℤ_[p]))ᵀ with hM
  have hMdet : IsUnit M.det := isUnit_det_transpose_map_cast _
    ((LinearMap.BilinForm.nondegenerate_iff_det_ne_zero (dualBasis p X)).1 hnd)
  -- The character of `F` with values `v` on the generators, for `v ≡ 1 mod p`.
  let ψ : ∀ v : X → ℤ_[p], (∀ i, (p : ℤ_[p]) ∣ v i - 1) → freeProP p X →ₜ* ℤ_[p]ˣ := fun v hv ↦
    characterOfUnits p X fun i ↦ unitsPrincipalMk one_ne_zero (by rw [pow_one]; exact hv i)
  have hψ : ∀ v hv i, ((ψ v hv (of i) : ℤ_[p]ˣ) : ℤ_[p]) = v i := fun v hv i ↦ by
    simp [ψ]
  -- The Newton map: the values on `r` of the Kronecker crossed homomorphisms for `ψ v`.
  let A : (X → ℤ_[p]) → X → ℤ_[p] := fun v ↦
    if hv : ∀ i, (p : ℤ_[p]) ∣ v i - 1 then fun j ↦ crossedHom (ψ v hv) (Pi.single j 1) r else 0
  have hA : ∀ v hv j, A v j = crossedHom (ψ v hv) (Pi.single j 1) r := fun v hv j ↦ by
    simp only [A, hv, implies_true, dite_true]
  -- Crossed homomorphisms vanish modulo `p` on the Frattini subgroup, so `A 1 ≡ 0 mod p`.
  have hone : ∀ i, (p : ℤ_[p]) ∣ (1 : X → ℤ_[p]) i - 1 := fun i ↦ by simp
  have h₀ : ∀ j, (p : ℤ_[p]) ∣ A 1 j := fun j ↦ by
    rw [hA 1 hone j]
    exact (isCrossedHom_crossedHom _ _).dvd_apply_of_mem_pLowerCentralSeries_one
      (isProP_freeProP p X) (continuous_crossedHom _ _) n.2
  -- The linearisation of the Newton map is the lifted matrix of the degree-one form.
  have hlin : ∀ v v' : X → ℤ_[p], (∀ i, (p : ℤ_[p]) ∣ v i - (1 : X → ℤ_[p]) i) →
      (∀ i, (p : ℤ_[p]) ∣ v' i - (1 : X → ℤ_[p]) i) → ∀ k : ℕ, 1 ≤ k →
      (∀ i, (p : ℤ_[p]) ^ k ∣ v' i - v i) →
      ∀ j, (p : ℤ_[p]) ^ (k + 1) ∣ A v' j - A v j - (M *ᵥ (v' - v)) j := by
    intro v v' hv hv' k _ hvv' j
    have hv₁ : ∀ i, (p : ℤ_[p]) ∣ v i - 1 := fun i ↦ by simpa using hv i
    have hv'₁ : ∀ i, (p : ℤ_[p]) ∣ v' i - 1 := fun i ↦ by simpa using hv' i
    rw [hA v hv₁ j, hA v' hv'₁ j]
    have key := pow_succ_dvd_crossedHom_single_sub_sub_mulVec (χ := ψ v hv₁) (χ' := ψ v' hv'₁)
      (fun i ↦ by rw [hψ v' hv'₁, hψ v hv₁]; exact hvv' i) n j
    simp only [hψ] at key
    exact key
  -- Newton's method: the unique zero of `A` congruent to `1` modulo `p`.
  have : IsAdicComplete (Ideal.span {(p : ℤ_[p])}) ℤ_[p] := by
    rw [← PadicInt.maximalIdeal_eq_span_p]
    infer_instance
  obtain ⟨v, ⟨hv, hAv⟩, huniq⟩ :=
    IsAdicComplete.existsUnique_eq_zero_of_isUnit_det (p : ℤ_[p]) A hMdet 1 h₀ hlin
  have hv₁ : ∀ i, (p : ℤ_[p]) ∣ v i - 1 := fun i ↦ by simpa using hv i
  refine ⟨ψ v hv₁, ⟨fun i ↦ by rw [hψ v hv₁ i]; exact hv₁ i, fun j ↦ by rw [← hA v hv₁, hAv]; rfl⟩,
    fun χ' ⟨hχ', hχ'₀⟩ ↦ ?_⟩
  have hχ'₁ : ∀ i, (p : ℤ_[p]) ∣ (χ' (of i) : ℤ_[p]) - 1 := hχ'
  have hψ' : ψ (fun i ↦ (χ' (of i) : ℤ_[p])) hχ'₁ = χ' := hom_ext fun x ↦ Units.ext (hψ _ hχ'₁ x)
  have hveq : (fun i ↦ (χ' (of i) : ℤ_[p])) = v := huniq _
    ⟨fun i ↦ by simpa using hχ' i, funext fun j ↦ by rw [hA _ hχ'₁ j, hψ']; exact hχ'₀ j⟩
  rw [← hψ']
  exact hom_ext fun x ↦ Units.ext (by rw [hψ _ hχ'₁, hψ v hv₁]; exact congrFun hveq x)

section Presented

variable [Finite X] {r : freeProP p X}

/-- **A one-relator pro-`p` group whose relator has nondegenerate degree-one form has exactly one
continuous character with the prescription property** (Labute, Theorem 4, without normal forms).
Let `F` be the free pro-`p` group on a finite type `X` and `r ∈ Φ(F)` a relator whose class in
`gr_1(F)` has nondegenerate degree-one form. Then the presented group `⟨X ∣ r⟩` has exactly one
continuous character `χ : ⟨X ∣ r⟩ → ℤ_pˣ` with the prescription property, that is, exactly one
continuous character for which every continuous crossed homomorphism `F → ℤ_p` for the induced
character of `F` vanishes at `r` (the relator criterion,
`TauCeti.presentedProP.hasPrescriptionProperty_iff_forall_isCrossedHom_eq_zero`). -/
theorem existsUnique_hasPrescriptionProperty_presentedProP_of_nondegenerate
    (hr : r ∈ proPFrattini p (freeProP p X))
    (hnd : (degreeOneForm (gradedMk p (freeProP p X) 1
      ⟨r, (pLowerCentralSeries_one_eq_proPFrattini Fact.out).symm.le hr⟩)).Nondegenerate) :
    ∃! χ : presentedProP p X {r} →ₜ* ℤ_[p]ˣ, HasPrescriptionProperty χ := by
  classical
  have := Fintype.ofFinite X
  obtain ⟨χF, ⟨-, hZ⟩, huniq⟩ := existsUnique_character_forall_crossedHom_single_eq_zero hr hnd
  have hkill := (ContinuousMonoidHom.forall_isCrossedHom_apply_eq_zero_iff χF r).2 hZ
  -- In particular `χF - 1` kills `r`, so `χF` descends to the presented group.
  have hχr : χF r = 1 := by
    have h1 : IsCrossedHom χF fun g ↦ (χF g : ℤ_[p]) - 1 := isCrossedHom_iff.2 fun g h ↦ by
      rw [_root_.map_mul, Units.val_mul]
      ring
    exact Units.ext (sub_eq_zero.1 (hkill _
      ((Units.continuous_val.comp χF.continuous).sub continuous_const) h1))
  have hrel : ∀ s ∈ ({r} : Set (freeProP p X)), χF s = 1 := fun s hs ↦ by
    rw [Set.mem_singleton_iff.1 hs]
    exact hχr
  refine ⟨presentedProP.lift χF hrel, ?_, fun χ₂ hχ₂ ↦ ?_⟩
  · refine presentedProP.hasPrescriptionProperty_of_forall_isCrossedHom_eq_zero
      fun F hFc hF s hs ↦ ?_
    rw [Set.mem_singleton_iff.1 hs]
    rw [presentedProP.lift_comp_mk] at hF
    exact hkill F hFc hF
  -- Uniqueness: a character with the prescription property is trivial modulo `p` on the
  -- generators and has vanishing Kronecker values at `r`, hence equals `χF`.
  · refine presentedProP.hom_ext ?_
    rw [presentedProP.lift_comp_mk]
    refine huniq _ ⟨fun i ↦ ?_,
      (ContinuousMonoidHom.forall_isCrossedHom_apply_eq_zero_iff _ r).1 ?_⟩
    · have := mem_unitsPrincipal_iff.1
        ((presentedProP.isProP p X {r}).mem_unitsPrincipal_one χ₂ (presentedProP.mk p {r} (of i)))
      simpa using this
    · exact fun F hFc hF ↦ (presentedProP.hasPrescriptionProperty_iff_forall_isCrossedHom_eq_zero
        (Set.singleton_subset_iff.2 hr) χ₂).1 hχ₂ F hFc hF r rfl

end Presented

section Demushkin

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] (hG : IsDemushkin p G)
include hG

/-- **Labute's Theorem 4: a Demushkin group has exactly one continuous character with the
prescription property.** -/
theorem IsDemushkin.existsUnique_hasPrescriptionProperty :
    ∃! χ : G →ₜ* ℤ_[p]ˣ, HasPrescriptionProperty χ := by
  obtain ⟨r, hr, ⟨e⟩⟩ := hG.exists_mem_proPFrattini_continuousMulEquiv_presentedProP
    (ULift.{v} (Fin (demushkinRank hG)))
    (by rw [Nat.card_ulift, Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨χ, hχ, huniq⟩ := existsUnique_hasPrescriptionProperty_presentedProP_of_nondegenerate hr
    (hG.nondegenerate_degreeOneForm hr e)
  refine ⟨χ.comp (e.symm : G →ₜ* _), hχ.comp_equiv, fun χ' hχ' ↦ ?_⟩
  have h := huniq _ (hχ'.comp_equiv (e := e))
  refine ContinuousMonoidHom.ext fun g ↦ ?_
  have := DFunLike.congr_fun h (e.symm g)
  simpa using this

/-- **The canonical character (orientation) of a Demushkin group**: the unique continuous
character `χ : G → ℤ_pˣ` with the prescription property (Labute, Theorem 4). Its image is the
invariant that, together with the rank, classifies Demushkin groups. -/
noncomputable def demushkinCharacter : G →ₜ* ℤ_[p]ˣ :=
  hG.existsUnique_hasPrescriptionProperty.exists.choose

/-- The canonical character has the prescription property. -/
theorem hasPrescriptionProperty_demushkinCharacter :
    HasPrescriptionProperty (demushkinCharacter hG) :=
  hG.existsUnique_hasPrescriptionProperty.exists.choose_spec

/-- **The canonical character is the only continuous character with the prescription property.**
This is the uniqueness half of Labute's Theorem 4 and the normalization consumed by the marked
classification. -/
theorem HasPrescriptionProperty.eq_demushkinCharacter {χ : G →ₜ* ℤ_[p]ˣ}
    (hχ : HasPrescriptionProperty χ) : χ = demushkinCharacter hG :=
  hG.existsUnique_hasPrescriptionProperty.unique hχ (hasPrescriptionProperty_demushkinCharacter hG)

/-- A continuous character of a Demushkin group has the prescription property exactly when it is
the canonical character. -/
@[simp]
theorem hasPrescriptionProperty_iff_eq_demushkinCharacter (χ : G →ₜ* ℤ_[p]ˣ) :
    HasPrescriptionProperty χ ↔ χ = demushkinCharacter hG :=
  ⟨fun h ↦ h.eq_demushkinCharacter hG, fun h ↦ h ▸ hasPrescriptionProperty_demushkinCharacter hG⟩

/-- The canonical character takes values in the principal units `1 + pℤ_p`. -/
theorem demushkinCharacter_apply_mem_unitsPrincipal_one (g : G) :
    demushkinCharacter hG g ∈ unitsPrincipal p 1 :=
  hG.isProP.mem_unitsPrincipal_one _ g

/-- **The image of the canonical character is closed**: it is the image of a compact group under
a continuous map. -/
theorem isClosed_range_demushkinCharacter :
    IsClosed ((demushkinCharacter hG).toMonoidHom.range : Set ℤ_[p]ˣ) := by
  rw [MonoidHom.coe_range]
  exact (isCompact_range (demushkinCharacter hG).continuous).isClosed

variable {H : Type w} [Group H] [TopologicalSpace H]

/-- Pulling the canonical character back along a topological group isomorphism `e : H ≃ₜ* G` does
not change its image. The group `H` may live in any universe and need not be known to be
Demushkin. -/
theorem range_demushkinCharacter_comp_equiv (e : H ≃ₜ* G) :
    ((demushkinCharacter hG).comp (e : H →ₜ* G)).toMonoidHom.range =
      (demushkinCharacter hG).toMonoidHom.range :=
  MonoidHom.range_comp_of_surjective _ _ e.surjective

/-- **The image of the canonical character, read through an isomorphism**: if `e : G ≃ₜ* H` and
every continuous character of `H` with the prescription property has image `A`, then the canonical
character of `G` has image `A`. This is how the image table of the normal forms, stated for any
character with the prescription property of the presented group, is read on the canonical
character of a Demushkin group isomorphic to that presented group. -/
theorem range_demushkinCharacter_eq_of_equiv (e : G ≃ₜ* H) {A : Subgroup ℤ_[p]ˣ}
    (hA : ∀ χ : H →ₜ* ℤ_[p]ˣ, HasPrescriptionProperty χ → χ.toMonoidHom.range = A) :
    (demushkinCharacter hG).toMonoidHom.range = A := by
  rw [← range_demushkinCharacter_comp_equiv hG e.symm]
  exact hA _ (hasPrescriptionProperty_demushkinCharacter hG).comp_equiv

variable [IsTopologicalGroup H] [CompactSpace H] [TotallyDisconnectedSpace H]
  (hH : IsDemushkin p H)

/-- **The canonical character is invariant under topological isomorphism**: along `e : G ≃ₜ* H`,
the canonical character of `H` is the canonical character of `G` pulled back along `e⁻¹`. The two
groups may live in different universes. -/
theorem demushkinCharacter_of_equiv (e : G ≃ₜ* H) :
    demushkinCharacter hH = (demushkinCharacter hG).comp (e.symm : H →ₜ* G) :=
  (((hasPrescriptionProperty_demushkinCharacter hG).comp_equiv (e := e.symm)).eq_demushkinCharacter
    hH).symm

/-- **The image of the canonical character is invariant under topological isomorphism.** -/
theorem range_demushkinCharacter_of_equiv (e : G ≃ₜ* H) :
    (demushkinCharacter hH).toMonoidHom.range = (demushkinCharacter hG).toMonoidHom.range := by
  rw [demushkinCharacter_of_equiv hG hH e]
  exact range_demushkinCharacter_comp_equiv hG e.symm

end Demushkin

end TauCeti
