/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Symplectic.DiagonalTorus.RootDatum
public import TauCeti.GroupTheory.Perm.WreathProduct
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Group

/-!
# The Weyl group of the diagonal torus of the symplectic group

The Weyl group of the type `Cₘ` root datum `TauCeti.Symplectic.diagonalRootDatum` of `Sp₂ₘ` is the
hyperoctahedral group `Sym(Bool) ≀ Sym(m)` of signed permutations of the coordinates. This file
constructs that identification integrally, for every rank `m` including `m = 0`.

The comparison goes through the signed basis characters `± eₐ` of the character lattice. Every
root reflection permutes them: the long reflections in `± 2eᵢ` change the sign of `eᵢ`, the
reflections in `eᵢ - eⱼ` exchange `eᵢ` and `eⱼ`, and those in `± (eᵢ + eⱼ)` exchange `eᵢ` with
`-eⱼ`. Hence every Weyl element permutes the `2m` signed characters compatibly with negation, and
it is determined by that permutation. Conversely the sign changes and the transpositions generate
the hyperoctahedral group, so its imprimitive action on `Fin m × Bool` is exactly the image.

Only the Weyl group of the root datum is treated here; no normalizer of the diagonal torus in
`Sp₂ₘ` is computed.

## Main definitions

* `TauCeti.Symplectic.diagonalWreathProductMulEquivWeylGroup`: the multiplicative equivalence from
  `Sym(Bool) ≀ Sym(m)` to the Weyl group of `diagonalRootDatum`.

## Main results

* `TauCeti.Symplectic.diagonalWreathProductMulEquivWeylGroup_smul_single`: a signed permutation
  sends the character `n • eₐ` to `± n • e_{π a}`, the sign being its sign change at `π a`;
  `TauCeti.Symplectic.diagonalWreathProductMulEquivWeylGroup_smul_apply` is the same action in
  coordinates.
* `TauCeti.Symplectic.diagonalWreathProductMulEquivWeylGroup_inl_mulSingle_swap`: the sign change
  of the `i`-th coordinate is the reflection in the long root `2eᵢ`.
* `TauCeti.Symplectic.diagonalWreathProductMulEquivWeylGroup_inr_swap`: the transposition of the
  `i`-th and `j`-th coordinates is the reflection in the short root `eᵢ - eⱼ`.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Plate III (the Weyl group of `Cₘ`).
* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, Section 12.1.
* J. S. Milne, *Algebraic Groups* (2017), Example 21.2 and Section 21.1.

The shape of the comparison follows `TauCeti.SpecialLinear.diagonalPermMulEquivWeylGroup`, and
the hyperoctahedral group is `TauCeti.WreathProduct` with its imprimitive action.
-/

public section

namespace TauCeti.Symplectic

open GLSymplecticFin

universe u

noncomputable section

variable {m : ℕ}

/-- The signed basis character `± eₐ`: the sign is negative exactly when the `Bool` is `true`. -/
private def signedCharacter (z : Fin m × Bool) : ULift.{u} (Fin m) →₀ ℤ :=
  Finsupp.single (ULift.up z.1) (if z.2 then -1 else 1)

private theorem signedCharacter_apply (z : Fin m × Bool) (a : Fin m) :
    signedCharacter.{u} z (ULift.up a) = if a = z.1 then (if z.2 then -1 else 1) else 0 := by
  classical
  rw [signedCharacter, Finsupp.single_apply]
  simp only [ULift.up_inj, eq_comm]

private theorem signedCharacter_injective :
    Function.Injective (signedCharacter.{u} (m := m)) := by
  rintro ⟨a, s⟩ ⟨b, t⟩ h
  have hb := congrArg (fun x ↦ x (ULift.up b)) h
  simp only [signedCharacter_apply, ite_true] at hb
  have hab : b = a := by
    by_contra hab
    simp only [hab, ite_false] at hb
    cases t <;> simp at hb
  subst hab
  cases s <;> cases t <;> simp_all

private theorem signedCharacter_not (z : Fin m × Bool) :
    signedCharacter.{u} (z.1, !z.2) = -signedCharacter.{u} z := by
  rcases z with ⟨a, s⟩
  cases s <;> simp [signedCharacter]

private theorem swap_up (i j c : Fin m) :
    Equiv.swap (ULift.up.{u} i) (ULift.up j) (ULift.up c) = ULift.up (Equiv.swap i j c) := by
  simp only [Equiv.swap_apply_def, ULift.up_inj]
  split_ifs <;> rfl

/-- Reflection in the long root `2eᵢ` changes the sign of `eᵢ`. -/
private theorem reflection_positiveLong_signedCharacter (i : Fin m) (z : Fin m × Bool) :
    (diagonalRootDatum.{u} m).reflection (.positiveLong i) (signedCharacter z) =
      signedCharacter (z.1, if z.1 = i then !z.2 else z.2) := by
  rcases z with ⟨a, s⟩
  refine Finsupp.ext fun ⟨c⟩ ↦ ?_
  rw [diagonalRootDatum_reflection_positiveLong_apply]
  simp only [ULift.up_inj, signedCharacter_apply]
  cases s <;> split_ifs <;> simp_all

/-- Reflection in the short root `eᵢ - eⱼ` exchanges `eᵢ` and `eⱼ`. -/
private theorem reflection_difference_signedCharacter {i j : Fin m} (hij : i ≠ j)
    (z : Fin m × Bool) :
    (diagonalRootDatum.{u} m).reflection (.difference i j hij) (signedCharacter z) =
      signedCharacter (Equiv.swap i j z.1, z.2) := by
  refine Finsupp.ext fun ⟨c⟩ ↦ ?_
  rw [diagonalRootDatum_reflection_difference_apply, swap_up]
  simp only [signedCharacter_apply, Equiv.swap_apply_eq_iff]

/-- Each root reflection sends a signed basis character to a signed basis character. -/
private theorem exists_reflection_signedCharacter (p : RootSubgroupIndex m) (z : Fin m × Bool) :
    ∃ z', (diagonalRootDatum.{u} m).reflection p (signedCharacter z) = signedCharacter z' := by
  classical
  rcases z with ⟨a, s⟩
  cases p with
  | positiveLong i => exact ⟨_, reflection_positiveLong_signedCharacter i _⟩
  | negativeLong i =>
    refine ⟨(a, if a = i then !s else s), Finsupp.ext fun ⟨c⟩ ↦ ?_⟩
    rw [diagonalRootDatum_reflection_negativeLong_apply]
    simp only [ULift.up_inj, signedCharacter_apply]
    cases s <;> split_ifs <;> simp_all
  | difference i j hij => exact ⟨_, reflection_difference_signedCharacter hij _⟩
  | positiveSum i j hij =>
    refine ⟨(Equiv.swap i j a, if a = i ∨ a = j then !s else s), Finsupp.ext fun ⟨c⟩ ↦ ?_⟩
    rw [diagonalRootDatum_reflection_positiveSum_apply, swap_up]
    simp only [ULift.up_inj, signedCharacter_apply, Equiv.swap_apply_eq_iff]
    cases s <;> split_ifs <;> simp_all [Equiv.swap_apply_def]
  | negativeSum i j hij =>
    refine ⟨(Equiv.swap i j a, if a = i ∨ a = j then !s else s), Finsupp.ext fun ⟨c⟩ ↦ ?_⟩
    rw [diagonalRootDatum_reflection_negativeSum_apply, swap_up]
    simp only [ULift.up_inj, signedCharacter_apply, Equiv.swap_apply_eq_iff]
    cases s <;> split_ifs <;> simp_all [Equiv.swap_apply_def]

/-- Every Weyl element sends a signed basis character to a signed basis character. -/
private theorem exists_smul_signedCharacter (w : (diagonalRootDatum.{u} m).weylGroup)
    (z : Fin m × Bool) : ∃ z', w • signedCharacter z = signedCharacter z' := by
  obtain ⟨g, hg⟩ := w
  rw [Subgroup.mk_smul]
  induction hg using RootPairing.weylGroup.induction generalizing z with
  | mem p =>
    rw [RootPairing.Equiv.reflection_smul]
    exact exists_reflection_signedCharacter p z
  | one => exact ⟨z, one_smul _ _⟩
  | mul x y _ _ hx hy =>
    obtain ⟨z₁, h₁⟩ := hy z
    obtain ⟨z₂, h₂⟩ := hx z₁
    exact ⟨z₂, by rw [mul_smul, h₁, h₂]⟩

/-- The signed basis character to which a Weyl element sends a given one. -/
private def signedPermFun (w : (diagonalRootDatum.{u} m).weylGroup) (z : Fin m × Bool) :
    Fin m × Bool :=
  (exists_smul_signedCharacter w z).choose

private theorem smul_signedCharacter (w : (diagonalRootDatum.{u} m).weylGroup)
    (z : Fin m × Bool) : w • signedCharacter z = signedCharacter (signedPermFun w z) :=
  (exists_smul_signedCharacter w z).choose_spec

/-- The permutation of the signed basis characters induced by a Weyl element. -/
private def signedPermEquiv (w : (diagonalRootDatum.{u} m).weylGroup) :
    Equiv.Perm (Fin m × Bool) where
  toFun := signedPermFun w
  invFun := signedPermFun w⁻¹
  left_inv z := signedCharacter_injective.{u} <| by
    rw [← smul_signedCharacter, ← smul_signedCharacter, inv_smul_smul]
  right_inv z := signedCharacter_injective.{u} <| by
    rw [← smul_signedCharacter, ← smul_signedCharacter, smul_inv_smul]

/-- The permutation representation of the Weyl group on the signed basis characters. -/
private def signedPerm : (diagonalRootDatum.{u} m).weylGroup →* Equiv.Perm (Fin m × Bool) where
  toFun := signedPermEquiv
  map_one' := Equiv.ext fun z ↦ signedCharacter_injective.{u} <| by
    rw [Equiv.Perm.one_apply, signedPermEquiv, Equiv.coe_fn_mk, ← smul_signedCharacter, one_smul]
  map_mul' v w := Equiv.ext fun z ↦ signedCharacter_injective.{u} <| by
    simp only [signedPermEquiv, Equiv.Perm.mul_apply, Equiv.coe_fn_mk]
    rw [← smul_signedCharacter, ← smul_signedCharacter, ← smul_signedCharacter, mul_smul]

private theorem signedCharacter_signedPerm (w : (diagonalRootDatum.{u} m).weylGroup)
    (z : Fin m × Bool) : signedCharacter (signedPerm w z) = w • signedCharacter z :=
  (smul_signedCharacter w z).symm

private theorem signedPerm_injective : Function.Injective (signedPerm.{u} (m := m)) := by
  intro v w h
  refine RootPairing.weylGroup.ext fun x ↦ ?_
  induction x using Finsupp.induction_linear with
  | zero => rw [smul_zero, smul_zero]
  | add x y hx hy => rw [smul_add, smul_add, hx, hy]
  | single a n =>
    have hsingle : Finsupp.single a n = n • signedCharacter.{u} (a.down, false) := by
      simp [signedCharacter]
    rw [hsingle, smul_comm v n, smul_comm w n, ← signedCharacter_signedPerm,
      ← signedCharacter_signedPerm, h]

/-- The permutation of a Weyl element commutes with negation of the signed characters. -/
private theorem signedPerm_not (w : (diagonalRootDatum.{u} m).weylGroup) (z : Fin m × Bool) :
    signedPerm w (z.1, !z.2) = ((signedPerm w z).1, !(signedPerm w z).2) :=
  signedCharacter_injective.{u} <| by
    rw [signedCharacter_signedPerm, signedCharacter_not, signedCharacter_not,
      signedCharacter_signedPerm, smul_neg]

private theorem signedPerm_ofIdx_positiveLong (i : Fin m) :
    signedPerm (RootPairing.weylGroup.ofIdx (diagonalRootDatum.{u} m) (.positiveLong i)) =
      WreathProduct.imprimitiveToPerm (Equiv.Perm Bool) (Fin m) Bool
        (SemidirectProduct.inl (Pi.mulSingle i (Equiv.swap false true))) := by
  classical
  refine Equiv.ext fun ⟨a, s⟩ ↦ signedCharacter_injective.{u} ?_
  rw [signedCharacter_signedPerm, RootPairing.weylGroup.ofIdx_smul,
    RootPairing.Equiv.reflection_smul, reflection_positiveLong_signedCharacter]
  by_cases h : a = i
  · subst h
    cases s <;> simp
  · simp [h]

private theorem signedPerm_ofIdx_difference {i j : Fin m} (hij : i ≠ j) :
    signedPerm (RootPairing.weylGroup.ofIdx (diagonalRootDatum.{u} m) (.difference i j hij)) =
      WreathProduct.imprimitiveToPerm (Equiv.Perm Bool) (Fin m) Bool
        (SemidirectProduct.inr (Equiv.swap i j)) := by
  refine Equiv.ext fun z ↦ signedCharacter_injective.{u} ?_
  rw [signedCharacter_signedPerm, RootPairing.weylGroup.ofIdx_smul,
    RootPairing.Equiv.reflection_smul, reflection_difference_signedCharacter]
  simp

/-- The Weyl group acts on the signed characters exactly through the hyperoctahedral group. -/
private theorem range_signedPerm :
    (signedPerm.{u} (m := m)).range =
      (WreathProduct.imprimitiveToPerm (Equiv.Perm Bool) (Fin m) Bool).range := by
  classical
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, rfl⟩
    exact WreathProduct.mem_range_imprimitiveToPerm_bool_iff.mpr (signedPerm_not w)
  · rintro _ ⟨x, rfl⟩
    rw [← SemidirectProduct.inl_left_mul_inr_right x, map_mul]
    refine mul_mem ?_ ?_
    · -- The base group is generated by the sign changes of single coordinates.
      refine Subgroup.pi_mem_of_mulSingle_mem
        (H := signedPerm.range.comap ((WreathProduct.imprimitiveToPerm (Equiv.Perm Bool) (Fin m)
          Bool).comp SemidirectProduct.inl)) x.left fun i ↦ ?_
      rcases (by decide : ∀ e : Equiv.Perm Bool, e = 1 ∨ e = Equiv.swap false true)
        (x.left i) with h | h
      · rw [h, Pi.mulSingle_one]
        exact one_mem _
      · rw [h]
        exact ⟨_, signedPerm_ofIdx_positiveLong i⟩
    · -- The top group is generated by transpositions.
      induction x.right using Equiv.Perm.swap_induction_on with
      | one => rw [map_one, map_one]; exact one_mem _
      | swap_mul f i j hij hf =>
        rw [map_mul, map_mul]
        exact mul_mem ⟨_, signedPerm_ofIdx_difference hij⟩ hf

variable (m) in
/-- **The Weyl group of `Sp₂ₘ`.** The Weyl group of the type `Cₘ` root datum of the diagonal torus
of `Sp₂ₘ` is the hyperoctahedral group `Sym(Bool) ≀ Sym(m)` of signed permutations of the
coordinates. A signed permutation acts on the character lattice by permuting the coordinate
characters `eₐ` and changing their signs; see
`TauCeti.Symplectic.diagonalWreathProductMulEquivWeylGroup_smul_single`. -/
def diagonalWreathProductMulEquivWeylGroup :
    WreathProduct (Equiv.Perm Bool) (Fin m) ≃* (diagonalRootDatum.{u} m).weylGroup :=
  ((MonoidHom.ofInjective
      (WreathProduct.imprimitiveToPerm_injective (Equiv.Perm Bool) (Fin m) Bool)).trans
    (MulEquiv.subgroupCongr range_signedPerm.symm)).trans
      (MonoidHom.ofInjective signedPerm_injective).symm

private theorem signedPerm_diagonalWreathProductMulEquivWeylGroup
    (w : WreathProduct (Equiv.Perm Bool) (Fin m)) :
    signedPerm (diagonalWreathProductMulEquivWeylGroup.{u} m w) =
      WreathProduct.imprimitiveToPerm (Equiv.Perm Bool) (Fin m) Bool w := by
  rw [diagonalWreathProductMulEquivWeylGroup, MulEquiv.trans_apply,
    MonoidHom.apply_ofInjective_symm]
  simp [MonoidHom.ofInjective_apply]

/-- A signed permutation `w` sends the character `n • eₐ` to `± n • e_{π a}`, where `π` is the
permutation `w.right` of the coordinates and the sign is negative exactly when `w` changes the
sign of the coordinate `π a`. -/
@[simp]
theorem diagonalWreathProductMulEquivWeylGroup_smul_single
    (w : WreathProduct (Equiv.Perm Bool) (Fin m)) (a : Fin m) (n : ℤ) :
    diagonalWreathProductMulEquivWeylGroup.{u} m w • Finsupp.single (ULift.up a) n =
      Finsupp.single (ULift.up (w.right a)) (if w.left (w.right a) false then -n else n) := by
  have hsingle : Finsupp.single (ULift.up.{u} a) n = n • signedCharacter.{u} (a, false) := by
    simp [signedCharacter]
  rw [hsingle, smul_comm, ← signedCharacter_signedPerm,
    signedPerm_diagonalWreathProductMulEquivWeylGroup, WreathProduct.imprimitiveToPerm_apply]
  split_ifs with h <;> simp [signedCharacter, h]

/-- In coordinates, a signed permutation `w` moves the `a`-th coordinate of a character to position
`π a`, where `π` is `w.right`, negating it exactly when `w` changes the sign of `π a`. -/
@[simp]
theorem diagonalWreathProductMulEquivWeylGroup_smul_apply
    (w : WreathProduct (Equiv.Perm Bool) (Fin m)) (x : ULift.{u} (Fin m) →₀ ℤ) (a : Fin m) :
    (diagonalWreathProductMulEquivWeylGroup.{u} m w • x) (ULift.up (w.right a)) =
      if w.left (w.right a) false then -x (ULift.up a) else x (ULift.up a) := by
  classical
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy =>
    rw [smul_add, Finsupp.add_apply, hx, hy]
    split_ifs <;> simp only [Finsupp.add_apply, neg_add]
  | single b n =>
    obtain ⟨b⟩ := b
    rw [diagonalWreathProductMulEquivWeylGroup_smul_single]
    simp only [Finsupp.single_apply, ULift.up_inj, (w.right).injective.eq_iff]
    split_ifs <;> simp_all

/-- The sign change of the `i`-th coordinate is the reflection in the long root `2eᵢ`. -/
@[simp]
theorem diagonalWreathProductMulEquivWeylGroup_inl_mulSingle_swap (i : Fin m) :
    diagonalWreathProductMulEquivWeylGroup.{u} m
        (SemidirectProduct.inl (Pi.mulSingle i (Equiv.swap false true))) =
      RootPairing.weylGroup.ofIdx (diagonalRootDatum.{u} m) (.positiveLong i) := by
  apply signedPerm_injective
  rw [signedPerm_diagonalWreathProductMulEquivWeylGroup, signedPerm_ofIdx_positiveLong]

/-- The transposition of the `i`-th and `j`-th coordinates is the reflection in the short root
`eᵢ - eⱼ`. -/
@[simp]
theorem diagonalWreathProductMulEquivWeylGroup_inr_swap {i j : Fin m} (hij : i ≠ j) :
    diagonalWreathProductMulEquivWeylGroup.{u} m (SemidirectProduct.inr (Equiv.swap i j)) =
      RootPairing.weylGroup.ofIdx (diagonalRootDatum.{u} m) (.difference i j hij) := by
  apply signedPerm_injective
  rw [signedPerm_diagonalWreathProductMulEquivWeylGroup, signedPerm_ofIdx_difference]

/-- The reflection in the long root `2eᵢ` is the sign change of the `i`-th coordinate. -/
@[simp]
theorem diagonalWreathProductMulEquivWeylGroup_symm_ofIdx_positiveLong (i : Fin m) :
    (diagonalWreathProductMulEquivWeylGroup.{u} m).symm
        (RootPairing.weylGroup.ofIdx (diagonalRootDatum.{u} m) (.positiveLong i)) =
      SemidirectProduct.inl (Pi.mulSingle i (Equiv.swap false true)) := by
  rw [MulEquiv.symm_apply_eq, diagonalWreathProductMulEquivWeylGroup_inl_mulSingle_swap]

/-- The reflection in the short root `eᵢ - eⱼ` is the transposition of the `i`-th and `j`-th
coordinates. -/
@[simp]
theorem diagonalWreathProductMulEquivWeylGroup_symm_ofIdx_difference {i j : Fin m}
    (hij : i ≠ j) :
    (diagonalWreathProductMulEquivWeylGroup.{u} m).symm
        (RootPairing.weylGroup.ofIdx (diagonalRootDatum.{u} m) (.difference i j hij)) =
      SemidirectProduct.inr (Equiv.swap i j) := by
  rw [MulEquiv.symm_apply_eq, diagonalWreathProductMulEquivWeylGroup_inr_swap hij]

end

end TauCeti.Symplectic
