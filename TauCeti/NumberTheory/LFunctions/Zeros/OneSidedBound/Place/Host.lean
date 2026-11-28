/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LFunctions.Zeros.OneSidedBound.HostField
public import TauCeti.NumberTheory.NumberField.CMType.Basic
public import TauCeti.NumberTheory.NumberField.Cyclotomic.InfinitePlace.Basic
import TauCeti.NumberTheory.Cyclotomic.Irreducible
import TauCeti.NumberTheory.NumberField.Cyclotomic.Finrank
import TauCeti.NumberTheory.Multiquadratic.Cyclotomic.FundamentalDiscriminant

/-!
# Infinite places of the cyclotomic host

The infinite places of `ℚ(√-d)(ζ)` are labeled by the units modulo the order of `ζ`.
Use the inclusion into `ℂ` as the reference embedding. The representative at each place
is the unique embedding extending the chosen inclusion of `ℚ(√-d)`; on `ζ` it acts by
raising to the power of the place label. This relates computations on residue labels to
archimedean data on the host field.

The labeling and representatives follow `New.Parameters.placeMulEquiv` and
`New.Parameters.galOfPlace` in `New/Reduction/Data/FieldsAndPlaces.lean` of lsernau/grh-lean
(commit `72fead102f663d5c7a407964a13dc0cf9d977207`). We use the discriminant support of the base
inside the `d`-th cyclotomic field to obtain irreducibility.
-/

public noncomputable section

open IntermediateField NumberField Polynomial IsCyclotomicExtension

namespace TauCeti.OneSidedBound.Parameters

variable (P : Parameters)

/-- The tower cyclotomic polynomial stays irreducible over `ℚ(√-d)`. -/
theorem irreducible_cyclotomic_baseField (s : ℕ) :
    Irreducible (cyclotomic (P.q₁ s) P.baseField) := by
  let ζ := Complex.exp (2 * Real.pi * Complex.I / (P.d : ℂ))
  have hζ : IsPrimitiveRoot ζ P.d := Complex.isPrimitiveRoot_exp _ P.prime_d.ne_zero
  have hK : P.baseField ≤ ℚ⟮ζ⟯ := by
    rw [P.baseField_eq_adjoin, adjoin_simple_le_iff]
    exact Multiquadratic.mem_of_sq_eq_of_isFundamentalDiscr P.prime_d.pos hζ
      (mem_adjoin_simple_self ℚ ζ) P.isFundamentalDiscr_neg_d (by simp) (by simp [sq])
  let : Algebra P.baseField ℚ⟮ζ⟯ := (inclusion hK).toRingHom.toAlgebra
  have : IsCyclotomicExtension {P.d} ℚ ℚ⟮ζ⟯ :=
    hζ.intermediateField_adjoin_isCyclotomicExtension ℚ
  have : NumberField ℚ⟮ζ⟯ := IsCyclotomicExtension.numberField {P.d} ℚ _
  have hdvd := Int.natAbs_dvd_natAbs.mpr (discr_dvd_discr P.baseField ℚ⟮ζ⟯)
  have hcop : (discr P.baseField).natAbs.Coprime (P.q₁ s) := by
    apply Nat.coprime_of_dvd
    intro p hp hpK hpq
    have hpd := Rat.prime_dvd_of_dvd_natAbs_discr ℚ⟮ζ⟯ P.d hp (hpK.trans hdvd)
    exact (Nat.not_coprime_of_dvd_of_dvd hp.one_lt hpq hpd) (P.coprime_q₁_d s)
  exact irreducible_cyclotomic_of_totient_le_finrank P.baseField (P.hostField s)
    (finrank_eq_totient P.baseField (P.hostField s) (P.q₁ s) hcop).ge

/-- Cyclotomic labels of the actual infinite places of the host, with label `1` at the
place of the inclusion into `ℂ`. -/
def hostPlaceEquiv (s : ℕ) : InfinitePlace (P.hostField s) ≃ (ZMod (P.q₁ s))ˣ :=
  (InfinitePlace.mk (algebraMap (P.hostField s) ℂ)).equivUnitsZMod
    (IsTotallyComplex.isUnramifiedAtInfinitePlaces (k := P.baseField) |>.isUnramified _)
    (P.irreducible_cyclotomic_baseField s)

/-- The inclusion into `ℂ` induces the place with label `1`. -/
@[simp] theorem hostPlaceEquiv_mk_algebraMap (s : ℕ) :
    P.hostPlaceEquiv s (InfinitePlace.mk (algebraMap (P.hostField s) ℂ)) = 1 := by
  simp [hostPlaceEquiv]

/-- The label of the place of the inclusion precomposed with a base-field automorphism
of the host is the cyclotomic character of that automorphism. -/
@[simp] theorem hostPlaceEquiv_mk_comp (s : ℕ) (σ : Gal(P.hostField s/P.baseField)) :
    P.hostPlaceEquiv s (InfinitePlace.mk ((algebraMap (P.hostField s) ℂ).comp σ)) =
      autEquivPow (P.hostField s) (P.irreducible_cyclotomic_baseField s) σ := by
  rw [hostPlaceEquiv, InfinitePlace.equivUnitsZMod_mk_comp]

/-- The place of a label is induced by precomposing the inclusion with the cyclotomic
automorphism for that label. -/
theorem hostPlaceEquiv_symm_apply (s : ℕ) (a : (ZMod (P.q₁ s))ˣ) :
    (P.hostPlaceEquiv s).symm a = InfinitePlace.mk ((algebraMap (P.hostField s) ℂ).comp
      ((autEquivPow (P.hostField s) (P.irreducible_cyclotomic_baseField s)).symm a)) := by
  apply (P.hostPlaceEquiv s).injective
  simp

/-- The CM type on the host consisting of embeddings extending the inclusion of the
imaginary quadratic base into `ℂ`. -/
def hostCMType (s : ℕ) : CMType (P.hostField s) :=
  (CMType.ofPair (algebraMap P.baseField ℂ)
    (by
      intro h
      exact (InfinitePlace.not_isReal_iff_isComplex.mpr (IsTotallyComplex.isComplex _))
        (InfinitePlace.isReal_mk_iff.mpr (ComplexEmbedding.isReal_iff.mpr h)))
    (fun ψ ↦ by
      rcases InfinitePlace.mk_eq_iff.mp (Subsingleton.elim
        (InfinitePlace.mk (algebraMap P.baseField ℂ)) (InfinitePlace.mk ψ)) with h | h
      · exact .inl h.symm
      · exact .inr (by simpa only [ComplexEmbedding.conjugate] using h.symm))).induced
    (algebraMap P.baseField (P.hostField s))

/-- Membership in the host CM type is exactly the restriction condition on the chosen base
embedding. -/
@[simp] theorem mem_hostCMType_iff (s : ℕ) {φ : P.hostField s →+* ℂ} :
    φ ∈ P.hostCMType s ↔
      φ.comp (algebraMap P.baseField (P.hostField s)) = algebraMap P.baseField ℂ := by
  simp [hostCMType, CMType.mem_induced]

/-- The representative of a place extends the chosen inclusion and acts via the cyclotomic
character of the place. -/
theorem hostCMType_embedding_eq (s : ℕ) (w : InfinitePlace (P.hostField s)) :
    (P.hostCMType s).embedding w = (algebraMap (P.hostField s) ℂ).comp
      ((autEquivPow (P.hostField s) (P.irreducible_cyclotomic_baseField s)).symm
        (P.hostPlaceEquiv s w)) := by
  conv_lhs => rw [← (P.hostPlaceEquiv s).symm_apply_apply w, P.hostPlaceEquiv_symm_apply]
  apply CMType.embedding_mk
  rw [P.mem_hostCMType_iff, RingHom.comp_assoc]
  ext x
  simp [← IsScalarTower.algebraMap_apply]

/-- The representative at `w` sends the chosen root of unity to the power specified by its
cyclotomic label. -/
@[simp] theorem hostCMType_embedding_hostRoot (s : ℕ) (w : InfinitePlace (P.hostField s)) :
    (P.hostCMType s).embedding w (P.hostRoot s) =
      (P.hostRoot s : ℂ) ^ (P.hostPlaceEquiv s w : ZMod (P.q₁ s)).val := by
  let e := autEquivPow (P.hostField s) (P.irreducible_cyclotomic_baseField s)
  have h : e.symm (P.hostPlaceEquiv s w) (P.hostRoot s) =
      P.hostRoot s ^ (e (e.symm (P.hostPlaceEquiv s w)) : ZMod (P.q₁ s)).val :=
    autEquivPow_apply_of_pow_eq_one (P.hostField s) (P.irreducible_cyclotomic_baseField s)
      (e.symm (P.hostPlaceEquiv s w)) (P.isPrimitiveRoot_hostRoot s).pow_eq_one
  rw [e.apply_symm_apply] at h
  simpa [P.hostCMType_embedding_eq, e] using congrArg (algebraMap (P.hostField s) ℂ) h

end TauCeti.OneSidedBound.Parameters
