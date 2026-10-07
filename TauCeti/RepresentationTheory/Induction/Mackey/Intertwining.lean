/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.DoubleCoset.Identity
public import TauCeti.RepresentationTheory.Induction.FrobeniusReciprocity
public import TauCeti.RepresentationTheory.Induction.Mackey.Hom

/-!
# The intertwining-number formula

Let `H` and `K` be subgroups of a finite group `G`.  Frobenius reciprocity moves a pairing of two
induced class functions down to `H`, and the Mackey decomposition then splits the restriction to
`H` of the function induced from `K` into a sum over the double cosets `H \ G / K`.  Applying
Frobenius reciprocity once more, inside `H`, to each summand gives

`⟨Ind_H^G f, Ind_K^G h⟩_G = ∑_{HsK} ⟨{}^s h, f⟩_{H ⊓ sKs⁻¹}`,

where `{}^s h` is the conjugate `y ↦ h (s⁻¹ y s)` of `h` on the Mackey subgroup and `f` is
restricted to that same subgroup. The corresponding decomposition of intertwining spaces gives
the **intertwining-number formula**, over every field,

`dim Hom_G(Ind_H^G A, Ind_K^G B) = ∑_{HsK} dim Hom_{H ⊓ sKs⁻¹}(Res A, {}^s B)`,

the quantitative core of the Mackey irreducibility criterion.

Taking `K = H` and `h = f`, the double coset of `1` is the class of every element of `H`, its
Mackey subgroup is all of `H`, and its term is the self-pairing `⟨f, f⟩_H`.  Splitting that term
off is `TauCeti.characterPairing_ind_ind_mackey_erase`, and
`TauCeti.finrank_hom_indFDRep_mackey_erase` is the same split for dimensions, where the term
becomes `dim End_H A`: this is the shape in which the Mackey irreducibility criterion reads the
formula.

A term of the sum is read at a representative `s` of its double coset, but does not depend on that
choice: replacing `s` by `h₁ s h₂` with `h₁ ∈ H` and `h₂ ∈ K` leaves the dimension unchanged
(`TauCeti.finrank_hom_res_mackeyToH_mul_left_mul_right`).

## Main statements

* `TauCeti.characterPairing_ind_ind_mackey`: the intertwining-number formula for class functions.
* `TauCeti.finrank_hom_indFDRep_mackey`: the intertwining-number formula as an identity of
  intertwining-space dimensions.
* `TauCeti.characterPairing_mackeyClassFunction_of_mem`: the term of a double coset meeting `H`
  is the self-pairing over `H`.
* `TauCeti.characterPairing_ind_ind_mackey_erase`: the formula for `K = H`, with the term of the
  identity double coset split off.
* `TauCeti.finrank_hom_indFDRep_mackey_erase`: the same split for intertwining-space dimensions,
  whose identity-coset term is `dim End_H A`.
* `TauCeti.finrank_hom_res_mackeyToH_one`: the Mackey term at the identity representative has
  the same dimension as the ordinary intertwining space over `H`.
* `TauCeti.finrank_hom_res_mackeyToH_of_normal`: for normal `H`, a Mackey term has the same
  dimension as the ordinary intertwining space from `A` to `{}^s A`.
* `TauCeti.finrank_hom_res_mackeyToH_mul_left_mul_right`: a term of the formula does not depend
  on the representative chosen for its double coset.

## Implementation notes

The formula is proved for class functions first and specialized to characters, exactly as
`TauCeti.frobenius_reciprocity_classFunction` is: no representation is involved in the class
function form, so it also covers class functions that are not characters.

The character pairing produces an identity in `k` of the *casts* of the dimensions, with
`Hom_G(Ind_K^G B, Ind_H^G A)` on the left. The natural-number formula instead uses
`FDRep.indHomMackeyLinearEquiv`, preserving the direction of Hom on both sides, and holds over
every field, including when `|G|` vanishes in `k`. Its self-intertwining specialization therefore
supplies the dimension formula for the Mackey irreducibility criterion in every characteristic.
The invariance of a single term under a change of representative is also proved by transporting
the intertwining space itself, and holds over any field.

The right-hand argument of each intertwining space is the representation `TauCeti.mackeySummand`
is induced from, written the way `TauCeti.mackeySummand` writes it: the restriction of `B` along
`TauCeti.mackeyToH`, which is the conjugate `{}^s B` restricted to the Mackey subgroup
(`TauCeti.mackeySummand_eq_indFDRep_res_conjFDRep` unfolds it into those two steps).

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.3, Proposition 22.
* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 5.
-/

public section

open scoped Pointwise

namespace TauCeti

universe u v

section ClassFunctions

variable {k : Type u} {G : Type v} [Field k] [Group G] {H K : Subgroup G}

open scoped Classical in
/-- **The intertwining-number formula for class functions.**  The pairing over `G` of a class
function induced from `H` with one induced from `K` is the sum, over the double cosets
`H \ G / K`, of the pairings over the Mackey subgroup `H ⊓ sKs⁻¹` of the conjugate `{}^s h` with
the restriction of `f`. -/
theorem characterPairing_ind_ind_mackey [Fintype G] (hG : IsUnit (Nat.card G : k))
    (f : ClassFunction k H) (h : ClassFunction k K) :
    ClassFunction.characterPairing (Subgroup.indClassFunction H f) (Subgroup.indClassFunction K h) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (K : Set G))
      ∑ D : DoubleCoset.Quotient (H : Set G) (K : Set G),
        ClassFunction.characterPairing (mackeyClassFunction D.out K H h)
          (ClassFunction.comap ((mackeySubgroup D.out K H).subgroupOf H).subtype f) := by
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (K : Set G))
  have hH : IsUnit (Nat.card H : k) := isUnit_natCard_subgroup H hG
  -- Both applications of Frobenius reciprocity are `characterPairing_ind`: the first moves the
  -- pairing from `G` down to `H`, the second moves each Mackey summand from `H` down to its
  -- Mackey subgroup.
  calc ClassFunction.characterPairing (Subgroup.indClassFunction H f) (Subgroup.indClassFunction K
    h)
      = ClassFunction.characterPairing f
          (ClassFunction.comap H.subtype (Subgroup.indClassFunction K h)) :=
        characterPairing_ind hG f (Subgroup.indClassFunction K h)
    _ = ClassFunction.characterPairing f
          (∑ D : DoubleCoset.Quotient (H : Set G) (K : Set G),
            Subgroup.indClassFunction ((mackeySubgroup D.out K H).subgroupOf H)
              (mackeyClassFunction D.out K H h)) := by
        rw [Subgroup.comap_subtype_indClassFunction_mackey]
    _ = ∑ D : DoubleCoset.Quotient (H : Set G) (K : Set G),
          ClassFunction.characterPairing f
            (Subgroup.indClassFunction ((mackeySubgroup D.out K H).subgroupOf H)
              (mackeyClassFunction D.out K H h)) :=
        map_sum (ClassFunction.characterPairing f) _ _
    _ = ∑ D : DoubleCoset.Quotient (H : Set G) (K : Set G),
          ClassFunction.characterPairing (mackeyClassFunction D.out K H h)
            (ClassFunction.comap ((mackeySubgroup D.out K H).subgroupOf H).subtype f) :=
        Finset.sum_congr rfl fun D _ => by
          rw [ClassFunction.characterPairing_symm]
          exact characterPairing_ind hH _ f

end ClassFunctions

section IdentityCoset

variable {k : Type u} {G : Type v} [Field k] [Group G] {H : Subgroup G}

open scoped Classical in
/-- **The term of a double coset that meets `H`.**  When the chosen representative lies in `H`, the
Mackey subgroup is all of `H`, conjugating by the representative does not change a class function,
and the term of `TauCeti.characterPairing_ind_ind_mackey` is the self-pairing `⟨f, f⟩_H`.

For `K = H` this is the term of the identity double coset, the one that
`TauCeti.characterPairing_ind_ind_mackey_erase` splits off. -/
theorem characterPairing_mackeyClassFunction_of_mem [Fintype H] {s : G} (hs : s ∈ H)
    (f : ClassFunction k H) :
    ClassFunction.characterPairing (mackeyClassFunction s H H f)
        (ClassFunction.comap ((mackeySubgroup s H H).subgroupOf H).subtype f) =
      ClassFunction.characterPairing f f := by
  have hcard : Nat.card ((mackeySubgroup s H H).subgroupOf H) = Nat.card H :=
    Nat.card_congr (mackeySubgroupSelfEquiv hs).toEquiv
  -- Conjugating by `s`, an element of `H`, leaves a class function on `H` unchanged.
  have hterm (y : (mackeySubgroup s H H).subgroupOf H) :
      f.1 (mackeyToH s H H y) = f.1 (mackeySubgroupSelfEquiv hs y) := by
    have hconj : (⟨s, hs⟩ : H)⁻¹ * (mackeySubgroupSelfEquiv hs y) * (⟨s, hs⟩ : H)⁻¹⁻¹
        = mackeyToH s H H y :=
      Subtype.ext (by simp [coe_mackeyToH_apply])
    rw [← hconj]
    exact ClassFunction.mem_iff.mp f.2 _ _
  rw [ClassFunction.characterPairing_apply, ClassFunction.characterPairing_apply, hcard]
  congr 1
  refine Fintype.sum_equiv (mackeySubgroupSelfEquiv hs).toEquiv _ _ fun y => ?_
  -- The identification is the identity on underlying elements, so it commutes with the inverse.
  have hinv : ((mackeySubgroup s H H).subgroupOf H).subtype y⁻¹
      = (mackeySubgroupSelfEquiv hs y)⁻¹ := by simp
  rw [mackeyClassFunction_coe, mackeyClassFun_apply, hterm y, ClassFunction.comap_apply, hinv]
  rfl

open scoped Classical in
/-- **The intertwining-number formula with the identity double coset split off.**  Inducing one
class function `f` from `H` to `G`, the self-pairing of the result is `⟨f, f⟩_H` plus the Mackey
terms of the remaining double cosets.

For the character of an irreducible representation over an algebraically closed field the first
summand is `1` (`TauCeti.ClassFunction.characterPairing_ofFDRep_self`), so the self-pairing of
`Ind_H^G f` is `1` exactly when the remaining terms *sum* to zero.  That the terms then vanish
one by one is a separate matter: `TauCeti.finrank_hom_indFDRep_mackey_erase` gives a formula
of natural-number dimensions over every field, where a zero sum forces every summand to vanish.
The character-pairing identity below separately assumes that the group order is invertible in
`k`; in positive characteristic, vanishing of the sum of dimension casts alone does not imply
vanishing of the dimensions. The natural-number formula underlies the Mackey irreducibility
criterion. -/
theorem characterPairing_ind_ind_mackey_erase [Fintype G] (hG : IsUnit (Nat.card G : k))
    (f : ClassFunction k H) :
    ClassFunction.characterPairing (Subgroup.indClassFunction H f) (Subgroup.indClassFunction H f) =
      ClassFunction.characterPairing f f +
        letI := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
        ∑ D ∈ Finset.univ.erase (DoubleCoset.mk H H 1),
          ClassFunction.characterPairing (mackeyClassFunction D.out H H f)
            (ClassFunction.comap ((mackeySubgroup D.out H H).subgroupOf H).subtype f) := by
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
  rw [characterPairing_ind_ind_mackey hG f f,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (DoubleCoset.mk H H 1)),
    characterPairing_mackeyClassFunction_of_mem
      ((doubleCosetMk_eq_mk_one_iff_mem H _).mp (DoubleCoset.out_eq' _)) f]

end IdentityCoset

section Representations

variable {k G : Type u} [Field k] [Group G] {H K : Subgroup G}

/-- The class function of the source of the Mackey summand -- the representation
`TauCeti.mackeySummand` is induced from, namely the conjugate `{}^s A` restricted to the Mackey
subgroup -- is the conjugated class function `TauCeti.mackeyClassFunction`. -/
@[simp]
theorem ofFDRep_res_mackeyToH (s : G) (H K : Subgroup G) (A : FDRep k H) :
    ClassFunction.ofFDRep ((Action.res (FGModuleCat k) (mackeyToH s H K)).obj A) =
      mackeyClassFunction s H K (ClassFunction.ofFDRep A) :=
  Subtype.ext <| funext fun y => by
    rw [ClassFunction.ofFDRep_apply, mackeyClassFunction_coe, mackeyClassFun_apply,
      ClassFunction.ofFDRep_apply, character_res_mackeyToH, mackeyClassFun_apply]

open scoped Classical in
/-- **The intertwining-number formula**, as an identity in `k` of the casts of the dimensions of
the intertwining spaces: the dimension of `Hom_G(Ind_K^G B, Ind_H^G A)` is the sum, over the double
cosets `H \ G / K`, of the dimensions of `Hom_{H ⊓ sKs⁻¹}(Res A, {}^s B)`.

The characteristic-free natural-number formula
`TauCeti.finrank_hom_indFDRep_mackey` instead uses `Hom_G(Ind_H^G A, Ind_K^G B)` on the left. -/
theorem natCast_finrank_hom_indFDRep_mackey [Finite G] (hG : IsUnit (Nat.card G : k))
    (A : FDRep k H) (B : FDRep k K) :
    (Module.finrank k (indFDRep B ⟶ indFDRep A) : k) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (K : Set G))
      ∑ D : DoubleCoset.Quotient (H : Set G) (K : Set G),
        (Module.finrank k (resFDRep ((mackeySubgroup D.out K H).subgroupOf H) A ⟶
          (Action.res (FGModuleCat k) (mackeyToH D.out K H)).obj B) : k) := by
  let := Fintype.ofFinite G
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (K : Set G))
  let : Invertible (Nat.card G : k) := hG.invertible
  rw [← ClassFunction.characterPairing_ofFDRep_eq_finrank,
    ← Subgroup.indClassFunction_ofFDRep, ← Subgroup.indClassFunction_ofFDRep,
    characterPairing_ind_ind_mackey hG _ _]
  refine Finset.sum_congr rfl fun D _ => ?_
  let : Invertible (Nat.card ((mackeySubgroup D.out K H).subgroupOf H) : k) :=
    (isUnit_natCard_subgroup _ (isUnit_natCard_subgroup H hG)).invertible
  rw [← ofFDRep_res_mackeyToH, ClassFunction.comap_subtype_ofFDRep,
    ClassFunction.characterPairing_ofFDRep_eq_finrank]

open scoped Classical in
/-- **The intertwining-number formula**, over every field:
`dim Hom_G(Ind_H^G A, Ind_K^G B) = ∑_{HsK} dim Hom_{H ⊓ sKs⁻¹}(Res A, {}^s B)`.

Applied with `K = H` and `B = A`, the identity double coset contributes `dim End_H A`, and the
formula is the quantitative core of the Mackey irreducibility criterion. -/
theorem finrank_hom_indFDRep_mackey [Finite G] (A : FDRep k H) (B : FDRep k K) :
    Module.finrank k (indFDRep A ⟶ indFDRep B) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (K : Set G))
      ∑ D : DoubleCoset.Quotient (H : Set G) (K : Set G),
        Module.finrank k (resFDRep ((mackeySubgroup D.out K H).subgroupOf H) A ⟶
          (Action.res (FGModuleCat k) (mackeyToH D.out K H)).obj B) := by
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (K : Set G))
  rw [(FDRep.indHomMackeyLinearEquiv A B).finrank_eq, Module.finrank_pi_fintype]

/-- At the identity representative, the Mackey intertwining space has the same dimension as the
ordinary intertwining space over the subgroup. -/
theorem finrank_hom_res_mackeyToH_one (A B : FDRep k H) :
    Module.finrank k
        (resFDRep ((mackeySubgroup 1 H H).subgroupOf H) A ⟶
          (Action.res (FGModuleCat k) (mackeyToH 1 H H)).obj B) =
      Module.finrank k (A ⟶ B) := by
  have hsubtype : ((mackeySubgroup 1 H H).subgroupOf H).subtype =
      (mackeySubgroupSelfEquiv (H := H) (s := (1 : G)) (one_mem H)).toMonoidHom := by
    ext y
    exact congrArg Subtype.val (coe_mackeySubgroupSelfEquiv_apply (H := H) (s := (1 : G))
      (one_mem H) y).symm
  have hmackey : mackeyToH 1 H H =
      (mackeySubgroupSelfEquiv (H := H) (s := (1 : G)) (one_mem H)).toMonoidHom := by
    ext y
    rw [coe_mackeyToH_apply]
    simp only [MulEquiv.coe_toMonoidHom]
    simpa only [inv_one, one_mul, mul_one] using
      congrArg Subtype.val (coe_mackeySubgroupSelfEquiv_apply
        (H := H) (s := (1 : G)) (one_mem H) y).symm
  let e := mackeySubgroupSelfEquiv (H := H) (s := (1 : G)) (one_mem H)
  have hsource : resFDRep ((mackeySubgroup 1 H H).subgroupOf H) A =
      (Action.res (FGModuleCat k) e.toMonoidHom).obj A :=
    congrArg (fun phi => (Action.res (FGModuleCat k) phi).obj A) (by simpa [e] using hsubtype)
  have htarget : (Action.res (FGModuleCat k) (mackeyToH 1 H H)).obj B =
      (Action.res (FGModuleCat k) e.toMonoidHom).obj B :=
    congrArg (fun phi => (Action.res (FGModuleCat k) phi).obj B) (by simpa [e] using hmackey)
  rw [hsource, htarget]
  exact finrank_hom_res_mulEquiv e A B

/-- For a normal subgroup, the dimension of a Mackey intertwining space equals the dimension of
the ordinary intertwining space from `A` to its conjugate `{}^s A`. -/
theorem finrank_hom_res_mackeyToH_of_normal [H.Normal] (A : FDRep k H) (s : G) :
    Module.finrank k (resFDRep ((mackeySubgroup s H H).subgroupOf H) A ⟶
        (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A) =
      Module.finrank k (A ⟶ conjNormalFDRep s A) := by
  let e := mackeySubgroupNormalEquiv (H := H) s
  have he_apply (y : (mackeySubgroup s H H).subgroupOf H) : e y = (y : H) :=
    coe_mackeySubgroupNormalEquiv_apply s y
  have hsubtype : ((mackeySubgroup s H H).subgroupOf H).subtype = e.toMonoidHom :=
    ((MulEquiv.toMonoidHom_eq_coe e).trans (coe_mackeySubgroupNormalEquiv s)).symm
  have hconj : mackeyToH s H H =
      (MulAut.conjNormal s⁻¹ : MulAut H).toMonoidHom.comp e.toMonoidHom := by
    ext y
    simp only [coe_mackeyToH_apply, MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom,
      Function.comp_apply]
    rw [he_apply]
    simp
  have hsource : resFDRep ((mackeySubgroup s H H).subgroupOf H) A =
      (Action.res (FGModuleCat k) e.toMonoidHom).obj A := by
    exact congrArg (fun φ => (Action.res (FGModuleCat k) φ).obj A) hsubtype
  have htarget : (Action.res (FGModuleCat k) (mackeyToH s H H)).obj A =
      (Action.res (FGModuleCat k) e.toMonoidHom).obj (conjNormalFDRep s A) := by
    rw [hconj, conjNormalFDRep, conjNormalFDRepFunctor]
    exact CategoryTheory.Functor.congr_obj (actionRes_comp _ _) A
  rw [hsource, htarget]
  exact finrank_hom_res_mulEquiv e A (conjNormalFDRep s A)

open CategoryTheory in
/-- **Conjugation intertwines two restrictions of one representation.**  If the two homomorphisms
`σ ∘ φ` and `σ'` from `M` to `L` differ by conjugation by `g : L`, in the sense that
`g * σ (φ y) = σ' y * g` for every `y`, then the automorphism `Action.ρAut A g` of the underlying
object meets the compatibility condition of `Action.mkIso` between the two restrictions of `A` they
name.  The source is written as a restriction along `φ` of a restriction along `σ` because that is
the shape a change of representative produces below. -/
private theorem res_ρ_comm_ρAut_hom {L M N : Type u} [Group L] [Monoid M] [Monoid N]
    (A : FDRep k L) (g : L) (φ : M →* N) (σ : N →* L) (σ' : M →* L)
    (hg : ∀ y : M, g * σ (φ y) = σ' y * g) (y : M) :
    ((Action.res (FGModuleCat k) φ).obj ((Action.res (FGModuleCat k) σ).obj A)).ρ y ≫
        (Action.ρAut A g).hom =
      (Action.ρAut A g).hom ≫ ((Action.res (FGModuleCat k) σ').obj A).ρ y := by
  -- Both restricted actions are, by the definition of `Action.res`, the action of `A` composed
  -- with the homomorphism, and this reads them that way.  `Action.res_obj_ρ` is not usable as a
  -- rewrite here: it rewrites the restricted action into one valued in `End A.V`, where the goal
  -- is composing endomorphisms of `((Action.res _ σ').obj A).V`, and those two objects agree only
  -- by unfolding `Action.res`, so the rewritten goal is rejected as not type-correct.  Stating the
  -- step once, here, is what keeps that reading out of the two isomorphisms built below.
  change Action.ρ A (σ (φ y)) ≫ Action.ρ A g = Action.ρ A g ≫ Action.ρ A (σ' y)
  rw [← End.mul_def, ← End.mul_def, ← map_mul, ← map_mul, hg]

open CategoryTheory in
/-- **The Mackey term depends only on the double coset**, as a dimension: the intertwining space
`Hom_{H ⊓ sKs⁻¹}(Res A, {}^s B)` has the same dimension at `s` and at `h₁ s h₂` for `h₁ ∈ H` and
`h₂ ∈ K`, which is exactly the change of representative of the double coset `HsK`.

Nothing is assumed of `k` beyond being a field: the two intertwining spaces are carried into one
another by the action of `h₁` on `A` and of `h₂` on `B`. -/
theorem finrank_hom_res_mackeyToH_mul_left_mul_right (A : FDRep k H) (B : FDRep k K) {h₁ h₂ : G}
    (hh₁ : h₁ ∈ H) (hh₂ : h₂ ∈ K) (s : G) :
    Module.finrank k (resFDRep ((mackeySubgroup (h₁ * s * h₂) K H).subgroupOf H) A ⟶
        (Action.res (FGModuleCat k) (mackeyToH (h₁ * s * h₂) K H)).obj B) =
      Module.finrank k (resFDRep ((mackeySubgroup s K H).subgroupOf H) A ⟶
        (Action.res (FGModuleCat k) (mackeyToH s K H)).obj B) := by
  -- Read both intertwining spaces over the Mackey subgroup of `s`, along the change of
  -- representative `mackeySubgroupOfCongr`, which conjugates by `h₁`.
  -- On the source, that conjugation is undone by the action of `h₁⁻¹`.  In both isomorphisms the
  -- three homomorphisms of `res_ρ_comm_ρAut_hom` are left to unification, which reads them off the
  -- ascribed type; naming them would only repeat that type.
  let α : (Action.res (FGModuleCat k) ((mackeySubgroupOfCongr hh₁ hh₂ s) : _ →* _)).obj
        (resFDRep ((mackeySubgroup (h₁ * s * h₂) K H).subgroupOf H) A) ≅
      resFDRep ((mackeySubgroup s K H).subgroupOf H) A :=
    Action.mkIso (Action.ρAut A (⟨h₁, hh₁⟩ : H)⁻¹) <|
      res_ρ_comm_ρAut_hom A (⟨h₁, hh₁⟩ : H)⁻¹ _ _ _ fun y => Subtype.ext (by
        simp only [MonoidHom.coe_ofClass, Subgroup.coe_subtype, coe_mackeySubgroupOfCongr_apply,
          Subgroup.coe_mul, Subgroup.coe_inv]
        group)
  -- and on the twisted target, where `h₁` cancels against the representative, by the action
  -- of `h₂`:
  let β : (Action.res (FGModuleCat k) ((mackeySubgroupOfCongr hh₁ hh₂ s) : _ →* _)).obj
        ((Action.res (FGModuleCat k) (mackeyToH (h₁ * s * h₂) K H)).obj B) ≅
      (Action.res (FGModuleCat k) (mackeyToH s K H)).obj B :=
    Action.mkIso (Action.ρAut B ⟨h₂, hh₂⟩) <|
      res_ρ_comm_ρAut_hom B ⟨h₂, hh₂⟩ _ _ _ fun y => Subtype.ext (by
        simp only [MonoidHom.coe_ofClass, coe_mackeyToH_apply, coe_mackeySubgroupOfCongr_apply,
          Subgroup.coe_mul]
        group)
  rw [← finrank_hom_res_mulEquiv (mackeySubgroupOfCongr hh₁ hh₂ s)]
  exact (Linear.homCongr k α β).finrank_eq

open scoped Classical in
/-- **The intertwining-number formula for a single induced representation**, over every field
and with the identity double coset split off:

`dim End_G(Ind_H^G A) = dim End_H A + ∑_{HsH ≠ H} dim Hom_{H ⊓ sHs⁻¹}(Res A, {}^s A)`.

All the summands are natural numbers, so `Ind_H^G A` has a one-dimensional endomorphism algebra
exactly when `A` does and every non-identity double coset contributes nothing. -/
theorem finrank_hom_indFDRep_mackey_erase [Finite G] (A : FDRep k H) :
    Module.finrank k (indFDRep A ⟶ indFDRep A) =
      Module.finrank k (A ⟶ A) +
        letI := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
        ∑ D ∈ Finset.univ.erase (DoubleCoset.mk H H 1),
          Module.finrank k (resFDRep ((mackeySubgroup D.out H H).subgroupOf H) A ⟶
            (Action.res (FGModuleCat k) (mackeyToH D.out H H)).obj A) := by
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (H : Set G))
  rw [finrank_hom_indFDRep_mackey A A,
    ← Finset.add_sum_erase _ _ (Finset.mem_univ (DoubleCoset.mk H H 1))]
  congr 1
  have hs : (DoubleCoset.mk H H 1).out ∈ H :=
    (doubleCosetMk_eq_mk_one_iff_mem H _).mp (DoubleCoset.out_eq' _)
  have he := finrank_hom_res_mackeyToH_mul_left_mul_right A A hs (one_mem H) 1
  rw [mul_one, mul_one] at he
  exact he.trans (finrank_hom_res_mackeyToH_one A A)

end Representations

end TauCeti
