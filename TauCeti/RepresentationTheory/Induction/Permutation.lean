/-
Copyright (c) 2026 Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RepresentationTheory.Character
public import TauCeti.RepresentationTheory.Induction.Projection
public import TauCeti.RepresentationTheory.Induction.Transitivity

/-!
# The permutation representation as an induced representation

For a subgroup `H` of a group `G`, inducing the trivial `H`-representation along `H.subtype`
gives the permutation representation of `G` on the left cosets `G ⧸ H`, and its character is the
number of fixed cosets, cast into the coefficient field.

More generally, for subgroups `D ≤ C ≤ G`, inducing the permutation representation of `C` on
`C ⧸ (D ⊓ C)` gives the permutation representation of `G` on `G ⧸ D`: a permutation
representation on cosets can be induced in stages.

Feeding the first identification into the projection formula of
`TauCeti/RepresentationTheory/Induction/Projection.lean` gives the classical description of
inducing a restricted representation, `Ind_H^G (Res_H^G Y) ≅ k[G ⧸ H] ⊗ Y`.

## Main definitions

* `TauCeti.indTrivialEquiv`: the equivalence of representations `Ind_H^G (trivial) ≃ k[G ⧸ H]`.
* `TauCeti.indTrivialIso`: the same statement in `Rep k G`.
* `TauCeti.indOfMulActionQuotientEquiv`: for `D ≤ C`, the equivalence of representations
  `Ind_C^G k[C ⧸ (D ⊓ C)] ≃ k[G ⧸ D]`.
* `TauCeti.indResProjection`: the corollary `Ind_H^G (Res_H^G Y) ≅ k[G ⧸ H] ⊗ Y` of the projection
  formula `TauCeti.indProjection`.

## Main statements

* `TauCeti.char_ofMulAction`: the character of a permutation representation at `g` is the
  number of points fixed by `g`, cast into `k`.
* `TauCeti.char_ind_trivial`: the character of `Ind_H^G (trivial)` at `g` is the number of
  cosets fixed by `g`, cast into `k`.

Both statements are equalities in `k`, so in positive characteristic they determine the fixed-point
count only modulo the characteristic.

## Implementation notes

Mathlib's `Representation.ind` is built as the coinvariants of `k[G] ⊗[k] A`, so the coset
orientation is a proof obligation rather than a convention: the `H`-action being quotiented out is
left translation on `k[G]`, whose orbits are the *right* cosets `Hx`, while `G` acts by right
translation by the inverse. The equivalence below therefore sends `⟦single x r ⊗ₜ a⟧` to
`single ⟦x⁻¹⟧ (a • r)`; inversion is what converts right cosets carrying a right action into
Mathlib's left-coset quotient `G ⧸ H` with its left action. In the same way
`TauCeti.indOfMulActionQuotientEquiv` sends `⟦single x 1 ⊗ₜ single ⟦c⟧ s⟧` to `single ⟦x⁻¹ * c⟧ s`.

## References

* J.-P. Serre, *Linear Representations of Finite Groups*, §2.1 (the permutation character) and
  §3.3 (inducing the unit representation, and the projection formula).
-/

public section

open CategoryTheory MonoidalCategory Representation TensorProduct
open scoped MonoidAlgebra

namespace TauCeti

universe u v w

section Induced

variable (k : Type u) [CommRing k] {G : Type v} [Group G] (H : Subgroup G)

/-- The `H`-representation on `k[G] ⊗[k] k` whose coinvariants define `Ind_H^G (trivial)`:
left translation by `H` on `k[G]`, and the trivial action on `k`. -/
private noncomputable abbrev indTrivialSource : Representation k H (k[G] ⊗[k] k) :=
  Representation.tprod ((Representation.leftRegular k G).comp H.subtype)
    (Representation.trivial k H k)

/-- The linear map `k[G] ⊗[k] k →ₗ[k] k[G ⧸ H]` sending `single x r ⊗ₜ a` to
`single ⟦x⁻¹⟧ (a • r)`. -/
private noncomputable def indTrivialLift : (k[G] ⊗[k] k) →ₗ[k] k[G ⧸ H] :=
  MonoidAlgebra.mapDomainLinearMap k k (fun x : G ↦ (QuotientGroup.mk x⁻¹ : G ⧸ H)) ∘ₗ
    (TensorProduct.rid k k[G]).toLinearMap

private theorem indTrivialLift_tmul (x : G) (r a : k) :
    indTrivialLift k H (MonoidAlgebra.single x r ⊗ₜ a) =
      MonoidAlgebra.single (QuotientGroup.mk x⁻¹ : G ⧸ H) (a • r) := by
  simp [indTrivialLift]

private theorem indTrivialLift_comp (s : H) :
    indTrivialLift k H ∘ₗ indTrivialSource k H s = indTrivialLift k H := by
  ext x
  simp [indTrivialLift]

/-- The forward map of `TauCeti.indTrivialEquiv`, from `Ind_H^G (trivial)` to `k[G ⧸ H]`. -/
private noncomputable def indTrivialToQuotient :
    IndV H.subtype (Representation.trivial k H k) →ₗ[k] k[G ⧸ H] :=
  Coinvariants.lift _ (indTrivialLift k H) (indTrivialLift_comp k H)

private theorem indTrivialToQuotient_mk (x : G) (a : k) :
    indTrivialToQuotient k H (IndV.mk H.subtype (Representation.trivial k H k) x a) =
      MonoidAlgebra.single (QuotientGroup.mk x⁻¹ : G ⧸ H) a := by
  simp [indTrivialToQuotient, IndV.mk, indTrivialLift_tmul]

/-- The image of a coset `⟦x⟧` in `Ind_H^G (trivial)`, namely `⟦single x⁻¹ 1 ⊗ₜ 1⟧`. -/
private noncomputable def indTrivialMk (q : G ⧸ H) :
    IndV H.subtype (Representation.trivial k H k) :=
  Quotient.liftOn' q
    (fun x : G ↦ IndV.mk H.subtype (Representation.trivial k H k) x⁻¹ (1 : k))
    fun _ b hab ↦ by
      simpa using (indV_mk_apply_inv H.subtype (Representation.trivial k H k)
        ⟨_, QuotientGroup.leftRel_apply.1 hab⟩ b⁻¹ 1).symm

private theorem indTrivialMk_mk (x : G) :
    indTrivialMk k H (QuotientGroup.mk x) =
      IndV.mk H.subtype (Representation.trivial k H k) x⁻¹ (1 : k) :=
  rfl

/-- The inverse map of `TauCeti.indTrivialEquiv`, from `k[G ⧸ H]` to `Ind_H^G (trivial)`. -/
private noncomputable def quotientToIndTrivial :
    k[G ⧸ H] →ₗ[k] IndV H.subtype (Representation.trivial k H k) :=
  Finsupp.linearCombination k (indTrivialMk k H) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

private theorem quotientToIndTrivial_single (q : G ⧸ H) (r : k) :
    quotientToIndTrivial k H (MonoidAlgebra.single q r) = r • indTrivialMk k H q := by
  simp [quotientToIndTrivial]

/-- **The permutation representation.** Inducing the trivial representation of a subgroup `H ≤ G`
along `H.subtype` gives the permutation representation of `G` on the left cosets `G ⧸ H`. -/
noncomputable def indTrivialEquiv : ((Representation.trivial k H k).ind H.subtype).Equiv
      (Representation.ofMulAction k G (G ⧸ H)) := by
  refine Representation.Equiv.mk
    (LinearEquiv.ofLinearMap (indTrivialToQuotient k H) (quotientToIndTrivial k H) ?_ ?_) ?_
  · refine MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext_ring ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp [quotientToIndTrivial_single, indTrivialMk_mk, indTrivialToQuotient,
        indTrivialLift_tmul]
  · refine IndV.hom_ext _ _ fun x ↦ LinearMap.ext_ring ?_
    simp [indTrivialToQuotient, indTrivialLift_tmul, quotientToIndTrivial_single,
      indTrivialMk_mk]
  · intro g
    refine IndV.hom_ext _ _ fun x ↦ LinearMap.ext_ring ?_
    simp [indTrivialToQuotient, indTrivialLift_tmul, ofMulAction_single, mul_inv_rev]

-- Not a `simp` lemma: `simp` unfolds the reducible `Representation.IndV.mk`, so the left-hand
-- side is not in `simp`-normal form.
/-- The generator computation rule for `TauCeti.indTrivialEquiv`. -/
theorem indTrivialEquiv_apply_mk (x : G) (a : k) :
    indTrivialEquiv k H (IndV.mk H.subtype (Representation.trivial k H k) x a) =
      MonoidAlgebra.single (QuotientGroup.mk x⁻¹ : G ⧸ H) a :=
  indTrivialToQuotient_mk k H x a

/-- The generator computation rule for the inverse of `TauCeti.indTrivialEquiv`. -/
@[simp]
theorem indTrivialEquiv_symm_apply_single (x : G) (r : k) :
    (indTrivialEquiv k H).symm (MonoidAlgebra.single (QuotientGroup.mk x : G ⧸ H) r) =
      r • IndV.mk H.subtype (Representation.trivial k H k) x⁻¹ (1 : k) :=
  quotientToIndTrivial_single k H _ r

/-- **The permutation representation**, in `Rep k G`: inducing the trivial representation of a
subgroup `H ≤ G` gives the permutation representation on the left cosets `G ⧸ H`. -/
noncomputable def indTrivialIso :
    Rep.ind H.subtype (Rep.trivial k H k) ≅ Rep.ofMulAction k G (G ⧸ H) :=
  Rep.mkIso (indTrivialEquiv k H)

-- Not a `simp` lemma: `simp` unfolds the reducible `Representation.IndV.mk`, so the left-hand
-- side is not in `simp`-normal form.
/-- The generator computation rule for `TauCeti.indTrivialIso`: it sends `⟦single x 1 ⊗ₜ a⟧` to
`single ⟦x⁻¹⟧ a`. -/
theorem indTrivialIso_hom_hom_apply_mk (x : G) (a : k) :
    (indTrivialIso k H).hom.hom (IndV.mk H.subtype (Representation.trivial k H k) x a) =
      MonoidAlgebra.single (QuotientGroup.mk x⁻¹ : G ⧸ H) a := by
  rw [indTrivialIso, Rep.mkIso_hom_hom_apply]
  exact indTrivialEquiv_apply_mk k H x a

-- `simp` reduces the carriers of the `abbrev`s `Rep.ind`, `Rep.trivial` and `Rep.ofMulAction`
-- in implicit type arguments before it looks a term up, so the left-hand side is stated through
-- `dsimp% only`, as in #8315.
/-- The computation rule for the inverse of `TauCeti.indTrivialIso` on the standard basis of
`k[G ⧸ H]`. -/
@[simp]
theorem indTrivialIso_inv_hom_apply_single (x : G) (r : k) :
    (dsimp% only
        ((indTrivialIso k H).inv.hom (MonoidAlgebra.single (QuotientGroup.mk x : G ⧸ H) r))) =
      r • IndV.mk H.subtype (Representation.trivial k H k) x⁻¹ (1 : k) := by
  rw [indTrivialIso, Rep.mkIso_inv_hom_apply]
  exact indTrivialEquiv_symm_apply_single k H x r

/-- `Ind_H^G (trivial)` is a finite module whenever `H` has finite index. -/
instance instFiniteIndTrivial [Finite (G ⧸ H)] :
    Module.Finite k (IndV H.subtype (Representation.trivial k H k)) :=
  Module.Finite.equiv (indTrivialEquiv k H).toLinearEquiv.symm

end Induced

section InducedQuotient

variable (k : Type u) [CommRing k] {G : Type v} [Group G] {C D : Subgroup G} (h : D ≤ C)

/-- The `C`-representation on `k[G] ⊗[k] k[C ⧸ (D ⊓ C)]` whose coinvariants define the induced
representation. -/
private noncomputable abbrev indQuotientSource :
    Representation k C (k[G] ⊗[k] k[C ⧸ D.subgroupOf C]) :=
  Representation.tprod ((Representation.leftRegular k G).comp C.subtype)
    (Representation.ofMulAction k C (C ⧸ D.subgroupOf C))

/-- The linear map `k[G] ⊗[k] k[C ⧸ (D ⊓ C)] →ₗ[k] k[G ⧸ D]` sending
`single x r ⊗ₜ single ⟦c⟧ s` to `single ⟦x⁻¹ * c⟧ (r * s)`. -/
private noncomputable def indQuotientLift :
    (k[G] ⊗[k] k[C ⧸ D.subgroupOf C]) →ₗ[k] k[G ⧸ D] :=
  TensorProduct.lift <|
    Finsupp.linearCombination k (fun x : G ↦
        MonoidAlgebra.mapDomainLinearMap k k <|
          Quotient.map' (fun c : C ↦ x⁻¹ * c) fun a b hab ↦ by
            simpa [QuotientGroup.leftRel_apply, mul_assoc, Subgroup.mem_subgroupOf] using hab) ∘ₗ
      (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

private theorem indQuotientLift_tmul (x : G) (r : k) (c : C) (s : k) :
    indQuotientLift k (MonoidAlgebra.single x r ⊗ₜ
        MonoidAlgebra.single (QuotientGroup.mk c : C ⧸ D.subgroupOf C) s) =
      MonoidAlgebra.single (QuotientGroup.mk (x⁻¹ * c) : G ⧸ D) (r * s) := by
  simp [indQuotientLift]

private theorem indQuotientLift_comp (c : C) :
    indQuotientLift k ∘ₗ indQuotientSource k c = indQuotientLift k (D := D) := by
  refine TensorProduct.ext <| MonoidAlgebra.lhom_ext' fun x ↦ LinearMap.ext_ring <|
    MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext_ring ?_
  induction q using QuotientGroup.induction_on with
  | H y => simp [indQuotientLift_tmul, Representation.ofMulAction_single, mul_assoc]

/-- The forward map of `TauCeti.indOfMulActionQuotientEquiv`, from `Ind_C^G k[C ⧸ (D ⊓ C)]` to
`k[G ⧸ D]`. -/
private noncomputable def indQuotientToQuotient :
    IndV C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) →ₗ[k] k[G ⧸ D] :=
  Coinvariants.lift _ (indQuotientLift k) (indQuotientLift_comp k)

include h in
/-- The image of a coset `⟦x⟧` in `Ind_C^G k[C ⧸ (D ⊓ C)]`, namely `⟦single x⁻¹ 1 ⊗ₜ single ⟦1⟧ 1⟧`.
It is well defined because `D ≤ C` fixes the coset `⟦1⟧`. -/
private noncomputable def indQuotientMk (q : G ⧸ D) :
    IndV C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) :=
  Quotient.liftOn' q
    (fun x : G ↦ IndV.mk C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) x⁻¹
      (MonoidAlgebra.single (QuotientGroup.mk 1) 1))
    fun a b hab ↦ by
      have hd : a⁻¹ * b ∈ D := QuotientGroup.leftRel_apply.1 hab
      let d : C := ⟨a⁻¹ * b, h hd⟩
      have hfix : Representation.ofMulAction k C (C ⧸ D.subgroupOf C) d⁻¹
          (MonoidAlgebra.single (QuotientGroup.mk 1) 1) =
            MonoidAlgebra.single (QuotientGroup.mk 1) 1 := by
        rw [Representation.ofMulAction_single, MulAction.Quotient.smul_mk, smul_eq_mul, mul_one]
        congr 1
        rw [QuotientGroup.eq]
        simpa [d] using Subgroup.mem_subgroupOf.2 hd
      have ha : a⁻¹ = C.subtype d * b⁻¹ := by simp [d]
      rw [ha, ← indV_mk_apply_inv, hfix]

private theorem indQuotientMk_mk (x : G) :
    indQuotientMk k h (QuotientGroup.mk x) =
      IndV.mk C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) x⁻¹
        (MonoidAlgebra.single (QuotientGroup.mk 1) 1) :=
  rfl

include h in
/-- The inverse map of `TauCeti.indOfMulActionQuotientEquiv`, from `k[G ⧸ D]` to
`Ind_C^G k[C ⧸ (D ⊓ C)]`. -/
private noncomputable def quotientToIndQuotient :
    k[G ⧸ D] →ₗ[k] IndV C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) :=
  Finsupp.linearCombination k (indQuotientMk k h) ∘ₗ
    (MonoidAlgebra.coeffLinearEquiv k).toLinearMap

private theorem quotientToIndQuotient_single (q : G ⧸ D) (r : k) :
    quotientToIndQuotient k h (MonoidAlgebra.single q r) = r • indQuotientMk k h q := by
  simp [quotientToIndQuotient]

include h in
/-- **Induction of a coset permutation representation.** For subgroups `D ≤ C ≤ G`, inducing the
permutation representation of `C` on its cosets `C ⧸ (D ⊓ C)` along `C.subtype` gives the
permutation representation of `G` on `G ⧸ D`. For `D = C` this is `TauCeti.indTrivialEquiv` up to
the identification of `k[C ⧸ ⊤]` with the trivial representation. -/
noncomputable def indOfMulActionQuotientEquiv :
    ((Representation.ofMulAction k C (C ⧸ D.subgroupOf C)).ind C.subtype).Equiv
      (Representation.ofMulAction k G (G ⧸ D)) := by
  refine Representation.Equiv.mk
    (LinearEquiv.ofLinearMap (indQuotientToQuotient k) (quotientToIndQuotient k h) ?_ ?_) ?_
  · refine MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext_ring ?_
    induction q using QuotientGroup.induction_on with
    | H x =>
      simp [quotientToIndQuotient_single, indQuotientMk_mk, indQuotientToQuotient,
        indQuotientLift_tmul]
  · refine IndV.hom_ext _ _ fun x ↦ MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext_ring ?_
    induction q using QuotientGroup.induction_on with
    | H c =>
      -- `⟦single x 1 ⊗ₜ single ⟦c⟧ 1⟧ = ⟦single (c⁻¹ * x) 1 ⊗ₜ single ⟦1⟧ 1⟧` in the coinvariants.
      simpa [quotientToIndQuotient_single, indQuotientMk_mk, indQuotientToQuotient,
        indQuotientLift_tmul, Representation.ofMulAction_single] using
        (indV_mk_apply_inv C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) c⁻¹ x
          (MonoidAlgebra.single (QuotientGroup.mk 1) 1)).symm
  · intro g
    refine IndV.hom_ext _ _ fun x ↦ MonoidAlgebra.lhom_ext' fun q ↦ LinearMap.ext_ring ?_
    induction q using QuotientGroup.induction_on with
    | H c =>
      simp [indQuotientToQuotient, indQuotientLift_tmul, Representation.ofMulAction_single,
        mul_assoc]

-- Not a `simp` lemma: `simp` unfolds the reducible `Representation.IndV.mk`, so the left-hand
-- side is not in `simp`-normal form.
/-- The generator computation rule for `TauCeti.indOfMulActionQuotientEquiv`: it sends
`⟦single x 1 ⊗ₜ single ⟦c⟧ s⟧` to `single ⟦x⁻¹ * c⟧ s`. -/
theorem indOfMulActionQuotientEquiv_apply_mk (x : G) (c : C) (s : k) :
    indOfMulActionQuotientEquiv k h
        (IndV.mk C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) x
          (MonoidAlgebra.single (QuotientGroup.mk c) s)) =
      MonoidAlgebra.single (QuotientGroup.mk (x⁻¹ * c) : G ⧸ D) s := by
  simp [indOfMulActionQuotientEquiv, indQuotientToQuotient, indQuotientLift_tmul]

/-- The generator computation rule for the inverse of `TauCeti.indOfMulActionQuotientEquiv`. -/
@[simp]
theorem indOfMulActionQuotientEquiv_symm_apply_single (x : G) (r : k) :
    (indOfMulActionQuotientEquiv k h).symm (MonoidAlgebra.single (QuotientGroup.mk x : G ⧸ D) r) =
      r • IndV.mk C.subtype (Representation.ofMulAction k C (C ⧸ D.subgroupOf C)) x⁻¹
        (MonoidAlgebra.single (QuotientGroup.mk 1) 1) :=
  quotientToIndQuotient_single k h _ r

end InducedQuotient

section Projection

variable {k : Type u} {G : Type u} [CommRing k] [Group G] {H : Subgroup G} (Y : Rep k G)

/-- **Induction of a restriction.** For a subgroup `H ≤ G`, restricting a `G`-representation to `H`
and inducing back up tensors it with the permutation representation on the cosets,
`Ind_H^G (Res_H^G Y) ≅ k[G ⧸ H] ⊗ Y`. This is `TauCeti.indProjection` applied to the trivial
`H`-representation, followed by `TauCeti.indTrivialIso`. -/
noncomputable def indResProjection :
    Rep.ind H.subtype (Rep.res H.subtype Y) ≅ Rep.ofMulAction k G (G ⧸ H) ⊗ Y :=
  (Rep.indFunctor k H.subtype).mapIso (λ_ (Rep.res H.subtype Y)).symm ≪≫
    indProjection H.subtype (𝟙_ (Rep k H)) Y ≪≫
    (indTrivialIso k H ⊗ᵢ Iso.refl Y)

/-- `TauCeti.indResProjection` on generators: the coset orientation is the one inherited from
`TauCeti.indTrivialIso`, which sends `⟦x ⊗ₜ a⟧` to `single ⟦x⁻¹⟧ a`. -/
theorem indResProjection_hom_hom_apply (x : G) (y : Y) :
    (indResProjection Y).hom.hom (IndV.mk H.subtype (Rep.res H.subtype Y).ρ x y)
      = MonoidAlgebra.single (QuotientGroup.mk x⁻¹ : G ⧸ H) (1 : k) ⊗ₜ[k] Y.ρ x⁻¹ y := by
  refine Eq.trans ?_ (congrArg (· ⊗ₜ[k] Y.ρ x⁻¹ y) (indTrivialIso_hom_hom_apply_mk k H x 1))
  refine Eq.trans ?_ (congrArg (Rep.Hom.hom (indTrivialIso k H ⊗ᵢ Iso.refl Y).hom)
    (indProjection_hom_hom_apply H.subtype (𝟙_ (Rep k H)) Y x 1 y))
  simp [indResProjection, Rep.indMap]

end Projection

section PermutationCharacter

variable (k : Type u) [Field k] {G : Type v} [Monoid G]

/-- **The permutation character.** The character of the permutation representation `k[X]` at `g`
is the number of points of `X` fixed by `g`, cast into `k`. -/
@[simp]
theorem char_ofMulAction (X : Type w) [MulAction G X] [Finite X] (g : G) :
    (Representation.ofMulAction k G X).character g = Nat.card {x : X // g • x = x} := by
  classical
  have := Fintype.ofFinite X
  rw [Representation.character,
    LinearMap.trace_eq_matrix_trace k (MonoidAlgebra.basis X k), Matrix.trace]
  simp [LinearMap.toMatrix_apply, MonoidAlgebra.basis, Finsupp.single_apply,
    Fintype.card_subtype]

end PermutationCharacter

section Character

variable (k : Type u) [Field k] {G : Type v} [Group G] (H : Subgroup G)

/-- **The permutation character of an induced trivial representation.** The character of
`Ind_H^G (trivial)` at `g` is the number of cosets in `G ⧸ H` fixed by `g`, cast into `k`. -/
@[simp]
theorem char_ind_trivial [Finite (G ⧸ H)] (g : G) :
    ((Representation.trivial k H k).ind H.subtype).character g =
      Nat.card {q : G ⧸ H // g • q = q} := by
  rw [Representation.char_iso (indTrivialEquiv k H), char_ofMulAction]

end Character

end TauCeti
