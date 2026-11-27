/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.NumberTheory.NumberField.CMField
public import TauCeti.NumberTheory.NumberField.Global.Ideles.Norm.Relative
public import TauCeti.RingTheory.DedekindDomain.FiniteAdeleRing.Residue
public import TauCeti.RingTheory.DedekindDomain.HeightOneSpectrumAction

/-!
# Weight-zero tame characters of norm-one ideles

For an extension `L / K`, a character of the kernel of the relative idele norm is automorphic if
it is trivial on the principal ideles in that kernel. A weight-zero tame datum at a finite set
`Q` records, in addition, a character of the residue-field units at each place in `Q`, whose
product gives the automorphic character on ideles with integral finite components. Outside `Q`
the residue character is understood to be trivial.

For a CM field and its maximal real subfield, a twist uses a set disjoint from its conjugate
and with norm prime to the level. It is an `m`-fold twist if every power with exponent from `1`
through `m`, at the *same* modulus, is nontrivial at each place of the modulus.

The conventions are those of `New.Data.TameChar` and `New.Data.MFoldTwist` in
`grh/src/New/Reduction/Data/LevelAndTwists.lean` of lsernau/grh-lean (`72fead1`).
-/

public section

open IsDedekindDomain NumberField
open IsDedekindDomain.FiniteAdeleRing (integralUnits)
open scoped Pointwise

namespace TauCeti.GlobalNumberFields

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- A weight-zero tame character of the norm-one ideles, with residue characters specified on
`Q`. A local character at a place of `Q` is allowed to become trivial under taking powers. -/
@[ext]
structure NormOneTameCharacter (Q : Finset (HeightOneSpectrum (𝓞 L))) where
  /-- The continuous character of the kernel of the relative idele norm. -/
  toContinuousMonoidHom : (ideleNormMap K L).toMonoidHom.ker →ₜ* Circle
  /-- The character kills rational norm-one points, i.e. principal ideles in the norm kernel. -/
  apply_principal (x : (ideleNormMap K L).toMonoidHom.ker)
      (hx : x.val ∈ IdeleGroup.principalSubgroup (𝓞 L) L) : toContinuousMonoidHom x = 1
  /-- The characters of the residue-field units at the places in the fixed modulus. -/
  residueCharacter (w : Q) :
    (IsLocalRing.ResidueField (w.val.adicCompletionIntegers L))ˣ →* Circle
  /-- On integral ideles, the character is exactly the product of the specified residue
  characters, with no archimedean contribution. -/
  apply_integral (x : (ideleNormMap K L).toMonoidHom.ker)
      (hx : IdeleGroup.toFiniteIdele (𝓞 L) L x.val ∈ integralUnits (𝓞 L) L) :
    toContinuousMonoidHom x = ∏ w : Q, residueCharacter w
      (w.val.integralUnitsReduction ⟨IdeleGroup.toFiniteIdele (𝓞 L) L x.val, hx⟩)

namespace NormOneTameCharacter

variable {K L} {Q : Finset (HeightOneSpectrum (𝓞 L))}

/-- The tame part at any finite place, extended by the trivial character outside the modulus. -/
noncomputable def residueCharacterAt (ξ : NormOneTameCharacter K L Q)
    (w : HeightOneSpectrum (𝓞 L)) :
    (IsLocalRing.ResidueField (w.adicCompletionIntegers L))ˣ →* Circle := by
  classical
  exact if hw : w ∈ Q then ξ.residueCharacter ⟨w, hw⟩ else 1

/-- Inside the modulus, the tame part is the specified residue character. -/
@[simp] theorem residueCharacterAt_of_mem (ξ : NormOneTameCharacter K L Q)
    {w : HeightOneSpectrum (𝓞 L)} (hw : w ∈ Q) :
    ξ.residueCharacterAt w = ξ.residueCharacter ⟨w, hw⟩ := by
  simp [residueCharacterAt, hw]

/-- Outside the modulus, the tame part is trivial. -/
@[simp] theorem residueCharacterAt_of_notMem (ξ : NormOneTameCharacter K L Q)
    {w : HeightOneSpectrum (𝓞 L)} (hw : w ∉ Q) : ξ.residueCharacterAt w = 1 := by
  simp [residueCharacterAt, hw]

/-- The trivial datum has trivial global and residue characters at every fixed modulus. -/
noncomputable instance : One (NormOneTameCharacter K L Q) where
  one :=
    { toContinuousMonoidHom := 1
      apply_principal := by simp
      residueCharacter := fun _ ↦ 1
      apply_integral := by simp }

/-- The global character of the trivial datum is trivial. -/
@[simp] theorem toContinuousMonoidHom_one :
    (1 : NormOneTameCharacter K L Q).toContinuousMonoidHom = 1 := (rfl)

/-- Each residue character of the trivial datum is trivial. -/
@[simp] theorem residueCharacter_one (w : Q) :
    (1 : NormOneTameCharacter K L Q).residueCharacter w = 1 := (rfl)

/-- Pointwise powers preserve automorphy and the weight-zero tame expansion, keeping the
modulus fixed even if a residue character becomes trivial. -/
noncomputable instance : Pow (NormOneTameCharacter K L Q) ℕ where
  pow ξ n :=
    { toContinuousMonoidHom := ξ.toContinuousMonoidHom ^ n
      apply_principal := by
        intro x hx
        simp [ξ.apply_principal x hx]
      residueCharacter := fun w ↦ ξ.residueCharacter w ^ n
      apply_integral := by
        intro x hx
        simp only [ContinuousMonoidHom.pow_apply, MonoidHom.pow_apply, ξ.apply_integral x hx,
          Finset.prod_pow] }

/-- Powers of the datum act by powers on the continuous character. -/
@[simp] theorem toContinuousMonoidHom_pow (ξ : NormOneTameCharacter K L Q) (n : ℕ) :
    (ξ ^ n).toContinuousMonoidHom = ξ.toContinuousMonoidHom ^ n := (rfl)

/-- Powers of the datum act by powers on each residue character. -/
@[simp] theorem residueCharacter_pow (ξ : NormOneTameCharacter K L Q) (n : ℕ) (w : Q) :
    (ξ ^ n).residueCharacter w = ξ.residueCharacter w ^ n := (rfl)

/-- Multiplication at a fixed modulus is pointwise on the global and residue characters. -/
noncomputable instance : Mul (NormOneTameCharacter K L Q) where
  mul ξ ψ :=
    { toContinuousMonoidHom := ξ.toContinuousMonoidHom * ψ.toContinuousMonoidHom
      apply_principal := by
        intro x hx
        simp [ξ.apply_principal x hx, ψ.apply_principal x hx]
      residueCharacter := fun w ↦ ξ.residueCharacter w * ψ.residueCharacter w
      apply_integral := by
        intro x hx
        simp only [ContinuousMonoidHom.mul_apply, MonoidHom.mul_apply, ξ.apply_integral x hx,
          ψ.apply_integral x hx, Finset.prod_mul_distrib] }

/-- The global character of a product is the product of the global characters. -/
@[simp] theorem toContinuousMonoidHom_mul (ξ ψ : NormOneTameCharacter K L Q) :
    (ξ * ψ).toContinuousMonoidHom = ξ.toContinuousMonoidHom * ψ.toContinuousMonoidHom := (rfl)

/-- At a place in the fixed modulus, the residue characters multiply pointwise. -/
@[simp] theorem residueCharacter_mul (ξ ψ : NormOneTameCharacter K L Q) (w : Q) :
    (ξ * ψ).residueCharacter w = ξ.residueCharacter w * ψ.residueCharacter w := (rfl)

/-- Tame data at a fixed modulus form a commutative monoid under pointwise multiplication.
The support of the nontrivial residue characters can shrink under multiplication. -/
noncomputable instance : CommMonoid (NormOneTameCharacter K L Q) :=
  Function.Injective.commMonoid (fun ξ ↦ (ξ.toContinuousMonoidHom, ξ.residueCharacter))
    (fun _ _ h ↦ NormOneTameCharacter.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
    rfl (fun _ _ ↦ rfl) (fun _ _ ↦ rfl)

/-- The trivial datum has trivial tame part at every finite place. -/
@[simp] theorem residueCharacterAt_one (w : HeightOneSpectrum (𝓞 L)) :
    (1 : NormOneTameCharacter K L Q).residueCharacterAt w = 1 := by
  by_cases hw : w ∈ Q <;> simp [hw]

/-- Extension by the trivial character commutes with multiplication. -/
@[simp] theorem residueCharacterAt_mul (ξ ψ : NormOneTameCharacter K L Q)
    (w : HeightOneSpectrum (𝓞 L)) :
    (ξ * ψ).residueCharacterAt w = ξ.residueCharacterAt w * ψ.residueCharacterAt w := by
  by_cases hw : w ∈ Q <;> simp [hw]

/-- Extension by the trivial character commutes with taking powers. -/
@[simp] theorem residueCharacterAt_pow (ξ : NormOneTameCharacter K L Q) (n : ℕ)
    (w : HeightOneSpectrum (𝓞 L)) : (ξ ^ n).residueCharacterAt w = ξ.residueCharacterAt w ^ n := by
  by_cases hw : w ∈ Q <;> simp [hw]

/-- The order of a residue character is positive, as the residue-field unit group is finite. -/
theorem orderOf_residueCharacter_pos (ξ : NormOneTameCharacter K L Q) (w : Q) :
    0 < orderOf (ξ.residueCharacter w) := by
  refine ((ξ.residueCharacter w).isOfFinOrder_iff_exists_pow_apply_eq_one.2 ?_).orderOf_pos
  refine ⟨Nat.card (IsLocalRing.ResidueField (w.val.adicCompletionIntegers L))ˣ,
    Nat.card_pos, fun u ↦ ?_⟩
  rw [← map_pow, pow_card_eq_one', map_one]

end NormOneTameCharacter

section CM

variable {L} [IsCMField L] {Q : Finset (HeightOneSpectrum (𝓞 L))}

/-- The modulus `Q` is permitted at level `M` if it is disjoint from its complex conjugate and
its norm (the product of the residue-field cardinalities) is prime to `M`. -/
def IsTwistModulus (Q : Finset (HeightOneSpectrum (𝓞 L))) (M : ℕ) : Prop :=
  Disjoint (Q : Set (HeightOneSpectrum (𝓞 L)))
    (IsCMField.complexConj L • (Q : Set (HeightOneSpectrum (𝓞 L)))) ∧
    Nat.Coprime (∏ w ∈ Q, w.asIdeal.absNorm) M

/-- The disjointness and level conditions on a twist modulus. -/
theorem isTwistModulus_iff (M : ℕ) :
    IsTwistModulus Q M ↔
      Disjoint (Q : Set (HeightOneSpectrum (𝓞 L)))
        (IsCMField.complexConj L • (Q : Set (HeightOneSpectrum (𝓞 L)))) ∧
        Nat.Coprime (∏ w ∈ Q, w.asIdeal.absNorm) M := (Iff.rfl)

/-- The empty modulus is permitted at every level. -/
@[simp] theorem isTwistModulus_empty (M : ℕ) :
    IsTwistModulus (L := L) ∅ M := by
  simp [isTwistModulus_iff]

namespace NormOneTameCharacter

/-- An `m`-fold twist has permitted modulus and every exponent `1 ≤ n ≤ m` gives a nontrivial
residue character at each place of that modulus. -/
def IsMFoldTwist (ξ : NormOneTameCharacter (maximalRealSubfield L) L Q) (M m : ℕ) : Prop :=
  IsTwistModulus Q M ∧ ∀ w : Q, ∀ n ∈ Finset.Icc 1 m, ξ.residueCharacter w ^ n ≠ 1

/-- A twist is a one-fold twist, so its residue characters are all nontrivial. -/
abbrev IsTwist (ξ : NormOneTameCharacter (maximalRealSubfield L) L Q) (M : ℕ) : Prop :=
  ξ.IsMFoldTwist M 1

/-- An `m`-fold twist has permitted modulus and no residue character becomes trivial under
the indicated powers. -/
theorem isMFoldTwist_iff {ξ : NormOneTameCharacter (maximalRealSubfield L) L Q} {M m : ℕ} :
    ξ.IsMFoldTwist M m ↔
      IsTwistModulus Q M ∧ ∀ w : Q, ∀ n ∈ Finset.Icc 1 m, ξ.residueCharacter w ^ n ≠ 1 :=
  (Iff.rfl)

/-- A twist at level `M` is exactly a tame character having permitted modulus and nontrivial
residue character at every place in the modulus. -/
theorem isTwist_iff {ξ : NormOneTameCharacter (maximalRealSubfield L) L Q} {M : ℕ} :
    ξ.IsTwist M ↔ IsTwistModulus Q M ∧ ∀ w : Q, ξ.residueCharacter w ≠ 1 := by
  simp [isMFoldTwist_iff]

/-- An `m`-fold twist gives a twist at each of its first `m` positive powers. -/
theorem IsMFoldTwist.isTwist_pow {ξ : NormOneTameCharacter (maximalRealSubfield L) L Q} {M m n : ℕ}
    (h : ξ.IsMFoldTwist M m) (hn : n ∈ Finset.Icc 1 m) : (ξ ^ n).IsTwist M := by
  obtain ⟨hQ, hχ⟩ := isMFoldTwist_iff.1 h
  exact isTwist_iff.2 ⟨hQ, fun w ↦ by simpa using hχ w n hn⟩

/-- Conversely, a permitted modulus and twists at each of the first `m` positive powers
suffice for an `m`-fold twist, including when `m = 0`. -/
theorem isMFoldTwist_iff_isTwist_pow {ξ : NormOneTameCharacter (maximalRealSubfield L) L Q}
    {M m : ℕ} : ξ.IsMFoldTwist M m ↔ IsTwistModulus Q M ∧
      ∀ n ∈ Finset.Icc 1 m, (ξ ^ n).IsTwist M := by
  constructor
  · exact fun h ↦ ⟨(isMFoldTwist_iff.1 h).1, fun _ hn ↦ h.isTwist_pow hn⟩
  · rintro ⟨hQ, hpow⟩
    refine isMFoldTwist_iff.2 ⟨hQ, fun w n hn ↦ ?_⟩
    simpa only [residueCharacter_pow] using (isTwist_iff.1 (hpow n hn)).2 w

/-- An `m`-fold twist uses a permitted modulus, and each residue character has order strictly
larger than `m`. -/
theorem isMFoldTwist_iff_orderOf {ξ : NormOneTameCharacter (maximalRealSubfield L) L Q}
    {M m : ℕ} : ξ.IsMFoldTwist M m ↔ IsTwistModulus Q M ∧
      ∀ w : Q, m < orderOf (ξ.residueCharacter w) := by
  rw [isMFoldTwist_iff]
  refine and_congr_right fun _ ↦ ⟨?_, ?_⟩
  · intro h w
    by_contra! hm
    exact h w _ (Finset.mem_Icc.2 ⟨ξ.orderOf_residueCharacter_pos w, hm⟩) (pow_orderOf_eq_one _)
  · intro h w n hn
    obtain ⟨hn₁, hnm⟩ := Finset.mem_Icc.1 hn
    exact pow_ne_one_of_lt_orderOf (by omega) (hnm.trans_lt (h w))

/-- The trivial character with empty modulus is an `m`-fold twist for every `m` and level. -/
@[simp] theorem isMFoldTwist_one_empty (M m : ℕ) :
    (1 : NormOneTameCharacter (maximalRealSubfield L) L ∅).IsMFoldTwist M m := by
  simp [isMFoldTwist_iff]

end NormOneTameCharacter

end CM

end TauCeti.GlobalNumberFields
