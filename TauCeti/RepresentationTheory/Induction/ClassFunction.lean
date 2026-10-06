/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.CharacterTable.ClassFunction
-- The translation action `g • (x : G ⧸ S)` occurs in the statements about which summands vanish.
public import Mathlib.GroupTheory.GroupAction.Quotient
-- Non-public: `TauCeti.smul_quotientGroup_mk_eq_self_iff` is used only inside a proof.
import TauCeti.GroupTheory.QuotientGroup.Basic
import TauCeti.GroupTheory.Coset.Basic

/-!
# The induced class function

Induction of representations along a finite-index subgroup `S ≤ G` sends a character of `S` to a
character of `G`, by the coset-representative formula
`TauCeti.character_indFDRep_sum_quotient`.  That formula makes sense for an arbitrary function on
`S`, and this file takes it as the definition of the **induced class function**
`TauCeti.indClassFun`.  It is the linearization of induction on characters, and the map that turns
the restriction/induction pair into an adjoint pair on class functions.

Nothing here mentions a representation, so the file sits below
`TauCeti.RepresentationTheory.Induction.Character`, which imports it to identify the induced
character with the induced class function of a character (`TauCeti.indClassFun_ofFDRep_character`)
and to deduce `TauCeti.character_ind` from `TauCeti.indClassFun_eq_natCard_inv_mul_sum`.

## Main definitions

* `TauCeti.indTerm f g x`: the summand attached to a representative `x`, namely `f (x⁻¹ g x)`
  when `x⁻¹ g x` lies in the subgroup and `0` otherwise.  It is the summand of the
  induced-character formula too, which the character file uses at `f = ρ.character`, together
  with the coset-invariance lemma `TauCeti.indTerm_eq_of_mk_eq` and the evaluations
  `TauCeti.indTerm_conj` and `TauCeti.indTerm_one`.
* `TauCeti.indClassFun S f`: the function `G → k` obtained from `f : S → k` by summing `f` over
  those left coset representatives that conjugate `g` into `S`.  There is no division by `|S|`,
  so it needs no invertibility hypothesis and no more than an additive commutative monoid of
  coefficients.
* `TauCeti.indClassFunAddHom S`: the same construction packaged as an additive map
  `(S → k) →+ (G → k)`, which is what lets a property be propagated through the additive
  generation of an `AddSubgroup` of functions.
* `TauCeti.ClassFunction.ind S`: the same construction packaged as a `k`-linear map
  `ClassFunction k S →ₗ[k] ClassFunction k G`.

## Main statements

* `TauCeti.indTerm_eq_zero_of_smul_mk_ne` and
  `TauCeti.indClassFun_eq_sum_of_smul_eq_self_mem`: only the cosets `g` fixes contribute, so the
  coset sum may be taken over any finite set of cosets containing the fixed ones.  This is what
  turns the formula into a finite explicit computation for a concrete group.
* `TauCeti.indTerm_eq_of_mk_eq_of_conj`: a summand depends only on its coset representative when
  the inducing function is invariant under conjugation in the subgroup.
* `TauCeti.indClassFun_conj` and `TauCeti.indClassFun_mem_classFunction`: induction preserves
  conjugation invariance over additive coefficients and sends class functions to class functions.
* `TauCeti.indClassFun_top` and `TauCeti.indClassFun_indClassFun_subgroupOf`: induction from `⊤`
  is the identity, and induction is transitive along `L ≤ T ≤ G`.
* `TauCeti.natCard_nsmul_indClassFun`: the additive group-sum form,
  `|S| • (Ind f)(g) = ∑_{x ∈ G} f(x⁻¹gx)`, and its averaged corollary
  `TauCeti.indClassFun_eq_natCard_inv_mul_sum`.
* `TauCeti.indClassFun_comp_subtype_mul`: the **projection formula**,
  `Ind_S^G ((Res_S f) · ψ) = f · Ind_S^G ψ` for a class function `f` of `G`.

Frobenius reciprocity for class functions, `⟨Ind f, h⟩_G = ⟨f, Res h⟩_S`, is
`TauCeti.frobenius_reciprocity_classFunction`; it needs the pairing, so it lives with the other
reciprocities in `TauCeti.RepresentationTheory.Induction.FrobeniusReciprocity`.

## Implementation notes

The definition sums over `Quotient.out` representatives of `G ⧸ S`, so it literally matches
`TauCeti.character_indFDRep_sum_quotient`.  For a general `f` the individual summands depend on
that choice of representatives; being a class function is a sufficient condition for them not to,
and that is what `TauCeti.indClassFun_mem_classFunction` extracts, in the form of conjugation
invariance of the total sum. The additive and scalar identities hold for arbitrary functions.

`TauCeti.indTerm` and the lemmas that evaluate it are shared, not internal to this file:
`TauCeti.RepresentationTheory.Induction.Character` sums it over right cosets and
`TauCeti.RepresentationTheory.Induction.FrobeniusReciprocity` sums it over all of `G`.
`TauCeti.indTerm_eq_of_mk_eq_of_conj` gives representative independence for explicitly
conjugation-invariant functions over coefficients with zero; `TauCeti.indTerm_eq_of_mk_eq`
specializes it to class functions.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, Chapter 7.2.
* I. M. Isaacs, *Character Theory of Finite Groups*, Chapter 5.
-/

public section

namespace TauCeti

universe u v

variable {k : Type u} {G : Type v} [Group G] {S : Subgroup G}

section Zero

variable [Zero k]

open scoped Classical in
/-- The summand of the induced class function attached to a representative `x`: the value of `f`
at `x⁻¹ * g * x` when that element lies in the subgroup, and `0` otherwise.

Specialized to the character of a representation of `S` this is the summand of the
induced-character formula `TauCeti.character_indFDRep_sum_quotient`. -/
noncomputable def indTerm (f : S → k) (g x : G) : k :=
  if h : x⁻¹ * g * x ∈ S then f ⟨x⁻¹ * g * x, h⟩ else 0

open scoped Classical in
/-- The defining case split of `TauCeti.indTerm`. -/
theorem indTerm_apply (f : S → k) (g x : G) :
    indTerm f g x = if h : x⁻¹ * g * x ∈ S then f ⟨x⁻¹ * g * x, h⟩ else 0 :=
  (rfl)

/-- **A summand vanishes unless `g` fixes the coset of its representative.**  The conjugate
`x⁻¹ g x` lies in `S` exactly when `g • xS = xS`, so only the fixed cosets contribute to
`TauCeti.indClassFun`. -/
theorem indTerm_eq_zero_of_smul_mk_ne (f : S → k) {g x : G}
    (h : g • (x : G ⧸ S) ≠ (x : G ⧸ S)) : indTerm f g x = 0 := by
  classical
  rw [indTerm, dite_eq_right fun hx => h (smul_quotientGroup_mk_eq_self_iff S g x |>.2 hx)]

/-- Conjugating the argument of the summand translates the representative. -/
theorem indTerm_conj (f : S → k) (g x c : G) :
    indTerm f (c * g * c⁻¹) x = indTerm f g (c⁻¹ * x) := by
  classical
  have h : x⁻¹ * (c * g * c⁻¹) * x = (c⁻¹ * x)⁻¹ * g * (c⁻¹ * x) := by group
  simp only [indTerm, h]

open scoped Classical in
/-- The value of the summand at the identity representative. -/
theorem indTerm_one (f : S → k) (g : G) :
    indTerm f g 1 = if h : g ∈ S then f ⟨g, h⟩ else 0 := by
  simp [indTerm]

/-- **A conjugation-invariant summand depends only on the left coset of its representative.**
This form of `TauCeti.indTerm_eq_of_mk_eq` needs only a zero in the coefficients and an explicit
conjugation-invariance hypothesis on `f`. -/
theorem indTerm_eq_of_mk_eq_of_conj {f : S → k}
    (hf : ∀ y s : S, f (s * y * s⁻¹) = f y) (g x y : G)
    (hxy : (QuotientGroup.mk x : G ⧸ S) = QuotientGroup.mk y) :
    indTerm f g x = indTerm f g y := by
  have hs : x⁻¹ * y ∈ S := QuotientGroup.leftRel_apply.mp (Quotient.exact' hxy)
  let s : S := ⟨x⁻¹ * y, hs⟩
  have hy : x * (s : G) = y := by simp [s]
  rw [← hy]
  classical
  by_cases hx : x⁻¹ * g * x ∈ S
  · have hxs : (x * (s : G))⁻¹ * g * (x * s) ∈ S := by
      simpa [mul_assoc] using S.mul_mem (S.mul_mem (S.inv_mem s.2) hx) s.2
    rw [indTerm, dite_eq_left hx, indTerm, dite_eq_left hxs]
    have helem : (⟨(x * (s : G))⁻¹ * g * (x * s), hxs⟩ : S) =
        s⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * s⁻¹⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
      group
    rw [helem, hf ⟨x⁻¹ * g * x, hx⟩ s⁻¹]
  · have hxs : (x * (s : G))⁻¹ * g * (x * s) ∉ S := by
      intro h
      exact hx (by simpa [mul_assoc] using S.mul_mem (S.mul_mem s.2 h) (S.inv_mem s.2))
    rw [indTerm, dite_eq_right hx, indTerm, dite_eq_right hxs]

private theorem indTerm_zero (g x : G) : indTerm (S := S) (0 : S → k) g x = 0 := by
  classical
  by_cases h : x⁻¹ * g * x ∈ S <;> simp [indTerm, h]

end Zero

section AddCommMonoid

variable [AddCommMonoid k]

open scoped Classical in
/-- **The induced class function.**  For `f : S → k` and `g : G`, sum `f (t⁻¹ g t)` over those
left coset representatives `t` of `S` in `G` with `t⁻¹ g t ∈ S`.

The sum has no division by `|S|`, so the definition needs nothing of the coefficients beyond
addition; the averaged group-sum form is `TauCeti.indClassFun_eq_natCard_inv_mul_sum`.  On a
character it is the character of the induced representation, by
`TauCeti.indClassFun_ofFDRep_character`.

The representatives are the fixed `Quotient.out` ones, so this is a function of `f` alone; and for a
conjugation-invariant `f` the individual summands, and hence the sum, are independent of the
representatives chosen.  `TauCeti.ClassFunction.ind` is the bundled form on
`TauCeti.ClassFunction k S`, and is the canonical API. -/
noncomputable def indClassFun (S : Subgroup G) [S.FiniteIndex] (f : S → k) : G → k := fun g =>
  letI := Fintype.ofFinite (G ⧸ S)
  ∑ t : G ⧸ S, indTerm f g (Quotient.out t)

open scoped Classical in
/-- The defining coset sum of `TauCeti.indClassFun`. -/
theorem indClassFun_apply [S.FiniteIndex] (f : S → k) (g : G) :
    indClassFun S f g =
      letI := Fintype.ofFinite (G ⧸ S)
      ∑ t : G ⧸ S,
        if h : (Quotient.out t)⁻¹ * g * Quotient.out t ∈ S then
          f ⟨(Quotient.out t)⁻¹ * g * Quotient.out t, h⟩
        else 0 :=
  (rfl)

/-- **The induced class function is a sum over the cosets that `g` fixes.**  The summand attached
to any other coset vanishes (`TauCeti.indTerm_eq_zero_of_smul_mk_ne`), so summing over a finite
set `T` of cosets that contains every fixed one already gives the whole sum.  In practice `T` is
the set of fixed cosets itself, which for a concrete group is a short explicit list. -/
theorem indClassFun_eq_sum_of_smul_eq_self_mem [S.FiniteIndex] (f : S → k) (g : G)
    (T : Finset (G ⧸ S)) (hT : ∀ t : G ⧸ S, g • t = t → t ∈ T) :
    indClassFun S f g = ∑ t ∈ T, indTerm f g (Quotient.out t) := by
  let := Fintype.ofFinite (G ⧸ S)
  refine ((Finset.sum_subset (Finset.subset_univ T) fun t _ ht => ?_).trans rfl).symm
  refine indTerm_eq_zero_of_smul_mk_ne f fun hfix => ht (hT t ?_)
  rwa [QuotientGroup.out_eq'] at hfix

/-! ### Additivity -/

private theorem indTerm_add (f₁ f₂ : S → k) (g x : G) :
    indTerm (f₁ + f₂) g x = indTerm f₁ g x + indTerm f₂ g x := by
  classical
  by_cases h : x⁻¹ * g * x ∈ S <;> simp [indTerm, h]

/-- Induction of functions commutes with every additive map of coefficients. The coset formula
uses only addition and zero, so no characteristic or invertibility hypothesis is needed. -/
@[simp]
theorem indClassFun_comp [S.FiniteIndex] {k' : Type*} [AddCommMonoid k']
    (φ : k →+ k') (f : S → k) :
    indClassFun S (φ ∘ f) = φ ∘ indClassFun S f := by
  classical
  funext g
  simp only [indClassFun_apply, Function.comp_apply, map_sum]
  apply Finset.sum_congr rfl
  intro t _
  split <;> simp

/-- Induction of class functions kills the zero function. -/
@[simp]
theorem indClassFun_zero [S.FiniteIndex] : indClassFun S (0 : S → k) = 0 := by
  funext g
  simp [indClassFun, indTerm_zero]

/-- Induction of class functions is additive. -/
@[simp]
theorem indClassFun_add [S.FiniteIndex] (f₁ f₂ : S → k) :
    indClassFun S (f₁ + f₂) = indClassFun S f₁ + indClassFun S f₂ := by
  funext g
  simp [indClassFun, indTerm_add, Finset.sum_add_distrib]

/-- **Induction of functions on a finite-index subgroup, as an additive map.**  It is
`TauCeti.indClassFun` bundled by the two lemmas above, which is what lets a property be propagated
through the additive generation of an `AddSubgroup` of functions; `TauCeti.ClassFunction.ind` is
the finer bundling, as a `k`-linear map on class functions. -/
noncomputable def indClassFunAddHom (S : Subgroup G) [S.FiniteIndex] :
    (S → k) →+ (G → k) where
  toFun := indClassFun S
  map_zero' := indClassFun_zero
  map_add' := indClassFun_add

@[simp]
theorem indClassFunAddHom_apply (S : Subgroup G) [S.FiniteIndex] (ψ : S → k) :
    indClassFunAddHom S ψ = indClassFun S ψ :=
  (rfl)

/-- Induction commutes with any scalar action preserving zero and addition. In particular,
this applies to module coefficients without requiring multiplication on the coefficients. -/
@[simp]
theorem indClassFun_smul [S.FiniteIndex] {R : Type*} [DistribSMul R k] (c : R) (f : S → k) :
    indClassFun S (c • f) = c • indClassFun S f :=
  indClassFun_comp (DistribSMul.toAddMonoidHom k c) f

/-! ### Conjugation invariance and transitivity -/

/-- Induction preserves conjugation invariance over any additive commutative monoid. -/
@[simp]
theorem indClassFun_conj [S.FiniteIndex] {f : S → k}
    (hf : ∀ y s, f (s * y * s⁻¹) = f y) (g c : G) :
    indClassFun S f (c * g * c⁻¹) = indClassFun S f g := by
  let := Fintype.ofFinite (G ⧸ S)
  calc indClassFun S f (c * g * c⁻¹)
      = ∑ t : G ⧸ S, indTerm f g (c⁻¹ * Quotient.out t) := by
        simp only [indClassFun, indTerm_conj]
    _ = indClassFun S f g :=
        Fintype.sum_equiv (MulAction.toPerm c⁻¹) _ _ fun t =>
          indTerm_eq_of_mk_eq_of_conj hf _ _ _ (QuotientGroup.mk_out_smul _ t).symm

/-- **Induction from the whole group is the identity**, read along `⊤ ≃ G`: the quotient by `⊤`
has a single coset. The inducing function need only be conjugation invariant, and the
coefficients need only form an additive commutative monoid. -/
@[simp]
theorem indClassFun_top {f : (⊤ : Subgroup G) → k} (hf : ∀ y s, f (s * y * s⁻¹) = f y)
    (g : G) : indClassFun ⊤ f g = f ⟨g, Subgroup.mem_top g⟩ := by
  let := Fintype.ofFinite (G ⧸ (⊤ : Subgroup G))
  have := QuotientGroup.subsingleton_quotient_top (G := G)
  rw [indClassFun, Fintype.sum_subsingleton _ (QuotientGroup.mk 1),
    indTerm_eq_of_mk_eq_of_conj hf g _ 1 (Subsingleton.elim _ _), indTerm_one,
    dite_eq_left (Subgroup.mem_top g)]

open scoped Classical in
/-- **Transitivity of induction.**  For subgroups `L ≤ T` with `L` of finite index, inducing a
conjugation-invariant function of `L` first to `T` and then to `G` is inducing it directly to `G`:
`Ind_T^G (Ind_L^T f) = Ind_L^G f`.  The intermediate step induces from `L` read as the subgroup
`L.subgroupOf T` of `T`, with `Subgroup.subgroupOfEquivOfLe` identifying the two.  That `T` has
finite index too follows from `L ≤ T` (`Subgroup.finiteIndex_of_le`), so it is not assumed.

Only an additive commutative monoid of coefficients is needed. -/
theorem indClassFun_indClassFun_subgroupOf {L T : Subgroup G} (hLT : L ≤ T) [L.FiniteIndex]
    {f : L → k} (hf : ∀ y s, f (s * y * s⁻¹) = f y) :
    haveI := Subgroup.finiteIndex_of_le hLT
    indClassFun T (indClassFun (L.subgroupOf T) fun x => f (Subgroup.subgroupOfEquivOfLe hLT x)) =
      indClassFun L f := by
  have := Subgroup.finiteIndex_of_le hLT
  funext g
  let := Fintype.ofFinite (G ⧸ T)
  let := Fintype.ofFinite (T ⧸ L.subgroupOf T)
  let := Fintype.ofFinite (G ⧸ L)
  -- At a fixed outer representative `x`, the summand of `Ind_T^G` is the inner coset sum.
  have hinner (x : G) : indTerm (indClassFun (L.subgroupOf T)
      fun y => f (Subgroup.subgroupOfEquivOfLe hLT y)) g x =
      ∑ s : T ⧸ L.subgroupOf T, indTerm f g (x * (s.out : T)) := by
    by_cases hx : x⁻¹ * g * x ∈ T
    · rw [indTerm, dite_eq_left hx, indClassFun]
      refine Finset.sum_congr rfl fun s _ => ?_
      have hconj : ((s.out⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * s.out : T) : G) =
          (x * (s.out : T))⁻¹ * g * (x * (s.out : T)) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        group
      by_cases hs : (x * (s.out : T))⁻¹ * g * (x * (s.out : T)) ∈ L
      · have hs' : s.out⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * s.out ∈ L.subgroupOf T := by
          rwa [Subgroup.mem_subgroupOf, hconj]
        rw [indTerm, dite_eq_left hs', indTerm, dite_eq_left hs]
        exact congrArg f (Subtype.ext hconj)
      · have hs' : s.out⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * s.out ∉ L.subgroupOf T := by
          rwa [Subgroup.mem_subgroupOf, hconj]
        rw [indTerm, dite_eq_right hs', indTerm, dite_eq_right hs]
    · -- If `x⁻¹ g x ∉ T`, no conjugate `(x s)⁻¹ g (x s)` with `s ∈ T` lies in `L ≤ T`.
      rw [indTerm, dite_eq_right hx]
      refine (Finset.sum_eq_zero fun s _ => ?_).symm
      have hs : (x * (s.out : T))⁻¹ * g * (x * (s.out : T)) ∉ L := fun h => hx <| by
        have := T.mul_mem (T.mul_mem (s.out : T).2 (hLT h)) (T.inv_mem (s.out : T).2)
        simpa [mul_assoc] using this
      rw [indTerm, dite_eq_right hs]
  calc indClassFun T _ g
      = ∑ t : G ⧸ T, ∑ s : T ⧸ L.subgroupOf T, indTerm f g (t.out * (s.out : T)) :=
        Finset.sum_congr rfl fun t _ => hinner t.out
    _ = indClassFun L f g := by
        rw [indClassFun, ← (Subgroup.mk_out_mul_out_bijective hLT).sum_comp
          (fun q : G ⧸ L => indTerm f g q.out), Fintype.sum_prod_type]
        refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
        exact indTerm_eq_of_mk_eq_of_conj hf _ _ _ (Quotient.out_eq' _).symm

/-! ### The group-sum form -/

open scoped Classical in
/-- **The group-sum form of the induced class function**, with no division: summing the
conjugation summand over all of `G` rather than over coset representatives adds `|S|` copies of the
induced value. No multiplication on the coefficients is needed. -/
theorem natCard_nsmul_indClassFun [Fintype G] {f : S → k}
    (hf : ∀ y s, f (s * y * s⁻¹) = f y) (g : G) :
    Nat.card S • indClassFun S f g =
      ∑ x : G, if h : x⁻¹ * g * x ∈ S then f ⟨x⁻¹ * g * x, h⟩ else 0 := by
  let := Fintype.ofFinite (G ⧸ S)
  let e : G ≃ (G ⧸ S) × S := Subgroup.groupEquivQuotientProdSubgroup
  have hterm (q : G ⧸ S) (s : S) : indTerm f g (e.symm (q, s)) = indTerm f g q.out := by
    refine indTerm_eq_of_mk_eq_of_conj hf _ _ _ ?_
    simpa only [e, Subgroup.groupEquivQuotientProdSubgroup_apply_fst,
      QuotientGroup.out_eq'] using congrArg Prod.fst (e.apply_symm_apply (q, s))
  calc Nat.card S • indClassFun S f g
      = ∑ q : G ⧸ S, ∑ _s : S, indTerm f g q.out := by
        simp [indClassFun, Finset.sum_nsmul]
    _ = ∑ q : G ⧸ S, ∑ s : S, indTerm f g (e.symm (q, s)) :=
        Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun s _ => (hterm q s).symm
    _ = ∑ x : G, indTerm f g x := by
        rw [← e.symm.sum_comp (fun x => indTerm f g x), Fintype.sum_prod_type]
    -- the remaining step only unfolds the summand
    _ = _ := rfl

end AddCommMonoid

section Semiring

variable [Semiring k]

/-! ### Conjugation invariance -/

section ClassFun

variable {f : S → k}

/-- The summand of the induced class function depends only on the left coset of its
representative. -/
theorem indTerm_eq_of_mk_eq (hf : f ∈ ClassFunction k S) (g x y : G)
    (hxy : (QuotientGroup.mk x : G ⧸ S) = QuotientGroup.mk y) :
    indTerm f g x = indTerm f g y :=
  indTerm_eq_of_mk_eq_of_conj (ClassFunction.mem_iff.mp hf) g x y hxy

/-- **The induced function of a class function is a class function.** -/
theorem indClassFun_mem_classFunction [S.FiniteIndex] (hf : f ∈ ClassFunction k S) :
    indClassFun S f ∈ ClassFunction k G :=
  ClassFunction.mem_iff.mpr (indClassFun_conj (ClassFunction.mem_iff.mp hf))

end ClassFun

/-! ### The projection formula -/

section Projection

variable {f : G → k}

/-- **The projection formula, on a single summand.**  The summand only ever evaluates a function on
`S` at a conjugate of `g`, so multiplying by the restriction of a class function `f` of `G`
multiplies the summand by the constant `f g`.

It is private: `TauCeti.indClassFun_comp_subtype_mul` is the projection formula every consumer
uses. -/
private theorem indTerm_comp_subtype_mul (hf : f ∈ ClassFunction k G) (ψ : S → k) (g x : G) :
    indTerm ((fun s : S => f s) * ψ) g x = f g * indTerm ψ g x := by
  classical
  by_cases h : x⁻¹ * g * x ∈ S
  · have hconj : f (x⁻¹ * g * x) = f g := by
      simpa using ClassFunction.mem_iff.mp hf g x⁻¹
    simp [indTerm, h, hconj]
  · simp [indTerm, h]

/-- **The projection formula for the induced class function**:
`Ind_S^G ((Res_S f) · ψ) = f · Ind_S^G ψ` for a class function `f` of `G` and an arbitrary
function `ψ` on `S`.

This is the class-function shadow of the tensor identity `TauCeti.indProjection`, and it is what
makes induction a map of modules over the ring of class functions: an induced function may be
multiplied by `f` either before or after inducing.  Only `f` is required to be a class function;
the identity is pointwise in `ψ`. -/
theorem indClassFun_comp_subtype_mul [S.FiniteIndex] (hf : f ∈ ClassFunction k G) (ψ : S → k) :
    indClassFun S ((fun s : S => f s) * ψ) = f * indClassFun S ψ := by
  funext g
  simp only [indClassFun, Pi.mul_apply, Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => indTerm_comp_subtype_mul hf ψ g _

end Projection

/-! ### The induced class function as a linear map -/

namespace ClassFunction

/-- **Induction of class functions**, packaged as a `k`-linear map
`ClassFunction k S →ₗ[k] ClassFunction k G`. -/
noncomputable def ind (S : Subgroup G) [S.FiniteIndex] :
    ClassFunction k S →ₗ[k] ClassFunction k G where
  toFun f := ⟨indClassFun S f.1, indClassFun_mem_classFunction f.2⟩
  map_add' f₁ f₂ := Subtype.ext (indClassFun_add f₁.1 f₂.1)
  map_smul' c f := Subtype.ext (indClassFun_smul c f.1)

@[simp]
theorem ind_apply [S.FiniteIndex] (f : ClassFunction k S) (g : G) :
    (ind S f).1 g = indClassFun S f.1 g :=
  (rfl)

end ClassFunction

end Semiring

/-! ### Averaging -/

section DivisionSemiring

variable [DivisionSemiring k]

open scoped Classical in
/-- **The averaged group-sum form of the induced class function.**  The order of the subgroup must
be invertible in the coefficient division semiring; without that hypothesis
`TauCeti.natCard_nsmul_indClassFun` is the division-free identity to use. -/
theorem indClassFun_eq_natCard_inv_mul_sum [Fintype G] {f : S → k}
    (hS : IsUnit (Nat.card S : k)) (hf : f ∈ ClassFunction k S) (g : G) :
    indClassFun S f g =
      (Nat.card S : k)⁻¹ * ∑ x : G, if h : x⁻¹ * g * x ∈ S then f ⟨x⁻¹ * g * x, h⟩ else 0 := by
  rw [← natCard_nsmul_indClassFun (ClassFunction.mem_iff.mp hf) g, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hS.ne_zero, one_mul]

end DivisionSemiring

end TauCeti
