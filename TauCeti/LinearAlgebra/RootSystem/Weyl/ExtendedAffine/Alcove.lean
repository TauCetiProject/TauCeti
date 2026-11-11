/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.RootSystem.Weyl.Affine.Alcove
public import TauCeti.LinearAlgebra.RootSystem.Weyl.ExtendedAffine.Basic

/-!
# The stabilizer of the fundamental alcove in the extended affine Weyl group

Let `b` be a base of a finite, reduced, irreducible, crystallographic root pairing `P`, with
fundamental alcove `A`, affine Weyl group `W_aff = Q∨ ⋊ W` and extended affine Weyl group
`W_ext = P∨ ⋊ W`. This file studies the stabilizer

`Ω = {f ∈ W_ext | f(A) = A}`

(`RootPairing.fundamentalAlcoveStabilizer`), the group of length-zero elements of `W_ext`.

Like `W_aff`, the group `W_ext` permutes the affine root hyperplanes `α = k`, so it permutes the
alcoves. Since `A` is a cell of the arrangement, an element of `W_ext` carrying one point of `A`
into `A` carries all of `A` onto `A`
(`RootPairing.mem_fundamentalAlcoveStabilizer_iff_apply_mem`).

Over an archimedean linearly ordered field `W_aff` is transitive on the alcoves
(`RootPairing.exists_mem_affineWeylGroup_apply_mem_fundamentalAlcove`), so every coset of `W_aff`
in `W_ext` meets `Ω`: `W_ext = W_aff ⊔ Ω`. Hence the homomorphism `W_ext → P∨ / Q∨` taking an
element to the class of its translation part is still onto when restricted to `Ω`: every class of
coweights modulo coroots has a representative in `Ω`, with translation part in that class. Its
kernel is `Ω ∩ W_aff`.

The affine Weyl group acts freely on the alcoves
(`RootPairing.eq_one_of_mem_affineWeylGroup_of_mapsTo`), so `Ω ∩ W_aff` is trivial and the
restricted homomorphism is injective. Over an archimedean linearly ordered field it is therefore an
isomorphism `Ω ≃ P∨ / Q∨` (`RootPairing.fundamentalAlcoveStabilizerEquivQuotient`).

## Main definitions

* `RootPairing.fundamentalAlcoveStabilizer`: the stabilizer `Ω` of the fundamental alcove in the
  extended affine Weyl group.
* `RootPairing.fundamentalAlcoveStabilizerToQuotient`: the homomorphism `Ω → P∨ / Q∨` taking an
  element to the class of its translation part.
* `RootPairing.fundamentalAlcoveStabilizerEquivQuotient`: **the isomorphism `Ω ≃ P∨ / Q∨`.**

## Main results

* `RootPairing.mem_fundamentalAlcoveStabilizer_iff_apply_mem`: an element of `W_ext` stabilizes
  the fundamental alcove as soon as it carries one point of it into it.
* `RootPairing.exists_mem_affineWeylGroup_mul_mem_fundamentalAlcoveStabilizer`: every element of
  `W_ext` is an element of `W_aff` times an element of `Ω`.
* `RootPairing.affineWeylGroup_sup_fundamentalAlcoveStabilizer`: `W_aff ⊔ Ω = W_ext`.
* `RootPairing.fundamentalAlcoveStabilizerToQuotient_surjective`: **`Ω → P∨ / Q∨` is onto.**
* `RootPairing.exists_mem_fundamentalAlcoveStabilizer_sub_mem_corootSpan`: every coweight `λ` is
  congruent modulo the coroot lattice to the translation part `ω 0` of some `ω ∈ Ω`.
* `RootPairing.ker_fundamentalAlcoveStabilizerToQuotient`: the kernel of `Ω → P∨ / Q∨` is
  `Ω ∩ W_aff`.
* `RootPairing.affineWeylGroup_subgroupOf_fundamentalAlcoveStabilizer_eq_bot`: `Ω ∩ W_aff` is
  trivial, and `RootPairing.fundamentalAlcoveStabilizerToQuotient_injective`: `Ω → P∨ / Q∨` is
  injective.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4–6*, Ch. VI, §2.3 (the group `Ω` of
  elements of the extended affine Weyl group stabilizing the fundamental alcove, and its
  isomorphism with `P(R∨) / Q(R∨)`).
* N. Iwahori and H. Matsumoto, *On some Bruhat decomposition and the structure of the Hecke rings
  of p-adic Chevalley groups*, Publ. Math. IHÉS 25 (1965), §1.
-/

public section

open Set

namespace RootPairing

section CommRing

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N]
  [Module R N] (P : RootPairing ι R M N) (b : P.Base)

/-! ### The stabilizer of the fundamental alcove -/

section Definition

variable [CharZero R] [Finite ι] [Nonempty ι] [Preorder R]

/-- The **stabilizer `Ω` of the fundamental alcove** in the extended affine Weyl group: the
elements `f` of `W_ext = P∨ ⋊ W` with `f(A) = A`, where `A` is the fundamental alcove of the base
`b`. -/
def fundamentalAlcoveStabilizer : Subgroup (N ≃ᵃ[R] N) where
  carrier :=
    {f | f ∈ P.extendedAffineWeylGroup ∧ f '' fundamentalAlcove P b = fundamentalAlcove P b}
  one_mem' := ⟨one_mem _, by simp⟩
  mul_mem' {f g} hf hg := ⟨mul_mem hf.1 hg.1, by
    rw [AffineEquiv.coe_mul, image_comp, hg.2, hf.2]⟩
  inv_mem' {f} hf := ⟨inv_mem hf.1, by
    conv_lhs => rw [← hf.2]
    simp [AffineEquiv.inv_def, image_image]⟩

/-- Membership in the stabilizer of the fundamental alcove. -/
@[simp]
theorem mem_fundamentalAlcoveStabilizer {f : N ≃ᵃ[R] N} :
    f ∈ P.fundamentalAlcoveStabilizer b ↔
      f ∈ P.extendedAffineWeylGroup ∧ f '' fundamentalAlcove P b = fundamentalAlcove P b :=
  Iff.rfl

/-- The stabilizer of the fundamental alcove is a subgroup of the extended affine Weyl group. -/
theorem fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup :
    P.fundamentalAlcoveStabilizer b ≤ P.extendedAffineWeylGroup := fun _ hf ↦ hf.1

end Definition

/-! ### Elements of `W_ext` meeting the fundamental alcove -/

section Alcove

variable [LinearOrder R] [IsStrictOrderedRing R] [Finite ι] [Nonempty ι] [P.IsCrystallographic]
  [P.IsReduced] [P.IsIrreducible] {P b}

/-- An element of the extended affine Weyl group carrying one point of the fundamental alcove into
the alcove carries every point of the alcove into it: it permutes the affine root hyperplanes, and
the alcove is a cell of their arrangement. -/
theorem apply_mem_fundamentalAlcove_of_mem_extendedAffineWeylGroup {f : N ≃ᵃ[R] N}
    (hf : f ∈ P.extendedAffineWeylGroup) {x y : N} (hx : x ∈ fundamentalAlcove P b)
    (hfx : f x ∈ fundamentalAlcove P b) (hy : y ∈ fundamentalAlcove P b) :
    f y ∈ fundamentalAlcove P b := by
  have hy' := (mem_fundamentalAlcove_iff_of_mem hx).mp hy
  exact (mem_fundamentalAlcove_iff_of_mem hfx).mpr fun j k ↦
    ⟨P.intCast_lt_root'_apply_iff_of_mem_extendedAffineWeylGroup hf (fun j k ↦ (hy' j k).1) j k,
      P.root'_apply_ne_intCast_of_mem_extendedAffineWeylGroup hf (fun j k ↦ (hy' j k).2) j k⟩

/-- **An element of the extended affine Weyl group stabilizes the fundamental alcove as soon as it
carries one point of the alcove into the alcove.** -/
theorem mem_fundamentalAlcoveStabilizer_iff_apply_mem {f : N ≃ᵃ[R] N} {x : N}
    (hx : x ∈ fundamentalAlcove P b) :
    f ∈ P.fundamentalAlcoveStabilizer b ↔
      f ∈ P.extendedAffineWeylGroup ∧ f x ∈ fundamentalAlcove P b := by
  refine ⟨fun hf ↦ ⟨hf.1, hf.2 ▸ mem_image_of_mem f hx⟩, fun ⟨hf, hfx⟩ ↦ ⟨hf, ?_⟩⟩
  refine (image_subset_iff.mpr fun y hy ↦
    apply_mem_fundamentalAlcove_of_mem_extendedAffineWeylGroup hf hx hfx hy).antisymm
    fun y hy ↦ ⟨f.symm y, ?_, f.apply_symm_apply y⟩
  -- `f⁻¹` carries the point `f x` of the alcove back to `x`.
  have hf' : f⁻¹ ∈ P.extendedAffineWeylGroup := inv_mem hf
  have hx' : f⁻¹ (f x) ∈ fundamentalAlcove P b := by
    rwa [AffineEquiv.inv_def, AffineEquiv.symm_apply_apply]
  simpa [AffineEquiv.inv_def] using
    apply_mem_fundamentalAlcove_of_mem_extendedAffineWeylGroup hf' hfx hx' hy

end Alcove

/-! ### The homomorphism `Ω → P∨ / Q∨` -/

section Quotient

variable [CharZero R] [Finite ι] [Nonempty ι] [Preorder R]

/-- The homomorphism from the stabilizer `Ω` of the fundamental alcove to `P∨ / (P∨ ∩ Q∨)` taking
an element to the class of its translation part `ω 0` modulo the coroot lattice; for a
crystallographic pairing the target is `P∨ / Q∨`. It is the restriction of
`RootPairing.extendedAffineWeylGroupToQuotient` to `Ω`. -/
def fundamentalAlcoveStabilizerToQuotient :
    P.fundamentalAlcoveStabilizer b →*
      Multiplicative (P.coweightLattice ⧸ (P.corootSpan ℤ).comap P.coweightLattice.subtype) :=
  P.extendedAffineWeylGroupToQuotient.comp
    (Subgroup.inclusion (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b))

@[simp]
lemma fundamentalAlcoveStabilizerToQuotient_apply (ω : P.fundamentalAlcoveStabilizer b) :
    P.fundamentalAlcoveStabilizerToQuotient b ω =
      .ofAdd (Submodule.Quotient.mk ⟨ω.1 0, (P.mem_extendedAffineWeylGroup_iff.1
        (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b ω.2)).2⟩) :=
  P.extendedAffineWeylGroupToQuotient_apply _

/-- The kernel of `Ω → P∨ / (P∨ ∩ Q∨)` is the part `Ω ∩ W_aff` of `Ω` lying in the affine Weyl
group. -/
theorem ker_fundamentalAlcoveStabilizerToQuotient :
    (P.fundamentalAlcoveStabilizerToQuotient b).ker =
      P.affineWeylGroup.subgroupOf (P.fundamentalAlcoveStabilizer b) := by
  ext ω
  rw [fundamentalAlcoveStabilizerToQuotient, ← MonoidHom.comap_ker,
    ker_extendedAffineWeylGroupToQuotient, Subgroup.mem_comap, Subgroup.mem_subgroupOf,
    Subgroup.mem_subgroupOf, Subgroup.coe_inclusion]

end Quotient

end CommRing

section Field

variable {ι R M N : Type*} [Field R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N} (b : P.Base) [LinearOrder R] [IsStrictOrderedRing R]
  [Finite ι] [Nonempty ι] [P.IsCrystallographic] [P.IsReduced] [P.IsIrreducible]

/-! ### `Ω ∩ W_aff` is trivial, and `Ω → P∨ / Q∨` is injective -/

/-- **The only element of the stabilizer of the fundamental alcove lying in the affine Weyl group
is the identity**: the affine Weyl group acts freely on the alcoves. -/
theorem affineWeylGroup_subgroupOf_fundamentalAlcoveStabilizer_eq_bot :
    P.affineWeylGroup.subgroupOf (P.fundamentalAlcoveStabilizer b) = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).mpr fun ω hω ↦ Subtype.ext ?_
  exact eq_one_of_mem_affineWeylGroup_of_mapsTo b (fundamentalAlcove_nonempty b)
    (Subgroup.mem_subgroupOf.mp hω) fun x hx ↦
      ((P.mem_fundamentalAlcoveStabilizer b).mp ω.2).2 ▸ mem_image_of_mem _ hx

/-- **The homomorphism `Ω → P∨ / Q∨` is injective**: its kernel `Ω ∩ W_aff` is trivial. -/
theorem fundamentalAlcoveStabilizerToQuotient_injective :
    Function.Injective (P.fundamentalAlcoveStabilizerToQuotient b) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_fundamentalAlcoveStabilizerToQuotient,
    affineWeylGroup_subgroupOf_fundamentalAlcoveStabilizer_eq_bot]

/-! ### `W_ext = W_aff ⊔ Ω`, and `Ω → P∨ / Q∨` is onto -/

variable [Archimedean R]

/-- **Every element of the extended affine Weyl group is an element of the affine Weyl group times
an element of the stabilizer of the fundamental alcove**: the affine Weyl group is transitive on
the alcoves, so it carries the alcove `f(A)` back to `A`. -/
theorem exists_mem_affineWeylGroup_mul_mem_fundamentalAlcoveStabilizer {f : N ≃ᵃ[R] N}
    (hf : f ∈ P.extendedAffineWeylGroup) :
    ∃ g ∈ P.affineWeylGroup, g * f ∈ P.fundamentalAlcoveStabilizer b := by
  obtain ⟨x, hx⟩ := fundamentalAlcove_nonempty b
  -- `f x` lies on no affine root hyperplane, since `f` permutes them.
  obtain ⟨g, hg, hgfx⟩ := exists_mem_affineWeylGroup_apply_mem_fundamentalAlcove b
    (P.root'_apply_ne_intCast_of_mem_extendedAffineWeylGroup hf
      (root'_ne_intCast_of_mem_fundamentalAlcove hx))
  exact ⟨g, hg, (mem_fundamentalAlcoveStabilizer_iff_apply_mem hx).mpr
    ⟨mul_mem (P.affineWeylGroup_le_extendedAffineWeylGroup hg) hf, hgfx⟩⟩

/-- **`W_ext = W_aff ⊔ Ω`**: the extended affine Weyl group is generated by the affine Weyl group
and the stabilizer of the fundamental alcove. -/
theorem affineWeylGroup_sup_fundamentalAlcoveStabilizer :
    P.affineWeylGroup ⊔ P.fundamentalAlcoveStabilizer b = P.extendedAffineWeylGroup := by
  refine le_antisymm (sup_le P.affineWeylGroup_le_extendedAffineWeylGroup
    (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b)) fun f hf ↦ ?_
  obtain ⟨g, hg, hgf⟩ := exists_mem_affineWeylGroup_mul_mem_fundamentalAlcoveStabilizer b hf
  rw [show f = g⁻¹ * (g * f) by group]
  exact mul_mem (Subgroup.mem_sup_left (inv_mem hg)) (Subgroup.mem_sup_right hgf)

/-- **The homomorphism `Ω → P∨ / Q∨` is onto**: every class of coweights modulo coroots is the
class of the translation part of an element of the stabilizer of the fundamental alcove. -/
theorem fundamentalAlcoveStabilizerToQuotient_surjective :
    Function.Surjective (P.fundamentalAlcoveStabilizerToQuotient b) := by
  intro q
  obtain ⟨f, rfl⟩ := P.extendedAffineWeylGroupToQuotient_surjective q
  obtain ⟨g, hg, hgf⟩ := exists_mem_affineWeylGroup_mul_mem_fundamentalAlcoveStabilizer b f.2
  refine ⟨⟨g * f, hgf⟩, ?_⟩
  -- `g` lies in the kernel `W_aff` of `W_ext → P∨ / Q∨`.
  have hg' : (⟨g, P.affineWeylGroup_le_extendedAffineWeylGroup hg⟩ : P.extendedAffineWeylGroup) ∈
      P.extendedAffineWeylGroupToQuotient.ker := by
    rw [ker_extendedAffineWeylGroupToQuotient, Subgroup.mem_subgroupOf]
    exact hg
  have h := map_mul P.extendedAffineWeylGroupToQuotient
    ⟨g, P.affineWeylGroup_le_extendedAffineWeylGroup hg⟩ f
  rw [MonoidHom.mem_ker.mp hg', one_mul] at h
  exact h

/-- **Every coweight is congruent modulo the coroot lattice to the translation part of an element
of `Ω`**: for each `λ` in the coweight lattice there is an `ω` stabilizing the fundamental alcove
with `ω 0 - λ` in the coroot lattice. -/
theorem exists_mem_fundamentalAlcoveStabilizer_sub_mem_corootSpan {v : N}
    (hv : v ∈ P.coweightLattice) :
    ∃ ω ∈ P.fundamentalAlcoveStabilizer b, ω 0 - v ∈ P.corootSpan ℤ := by
  obtain ⟨ω, hω⟩ := fundamentalAlcoveStabilizerToQuotient_surjective b
    (.ofAdd (Submodule.Quotient.mk ⟨v, hv⟩))
  rw [fundamentalAlcoveStabilizerToQuotient_apply, Multiplicative.ofAdd.injective.eq_iff,
    Submodule.Quotient.eq, Submodule.mem_comap] at hω
  exact ⟨ω, ω.2, by simpa using hω⟩

/-! ### `Ω ≃ P∨ / Q∨` -/

variable (P) in
/-- **The stabilizer of the fundamental alcove is isomorphic to `P∨ / Q∨`**, by the class of the
translation part `ω 0` modulo the coroot lattice: the coweight lattice modulo the coroot lattice,
written multiplicatively. -/
noncomputable def fundamentalAlcoveStabilizerEquivQuotient :
    P.fundamentalAlcoveStabilizer b ≃*
      Multiplicative (P.coweightLattice ⧸ (P.corootSpan ℤ).comap P.coweightLattice.subtype) :=
  MulEquiv.ofBijective (P.fundamentalAlcoveStabilizerToQuotient b)
    ⟨fundamentalAlcoveStabilizerToQuotient_injective b,
      fundamentalAlcoveStabilizerToQuotient_surjective b⟩

@[simp]
lemma fundamentalAlcoveStabilizerEquivQuotient_apply (ω : P.fundamentalAlcoveStabilizer b) :
    P.fundamentalAlcoveStabilizerEquivQuotient b ω = P.fundamentalAlcoveStabilizerToQuotient b ω :=
  (rfl)

/-- The representative chosen by the inverse quotient isomorphism has the prescribed coweight
class modulo the coroot lattice. -/
@[simp]
lemma ofAdd_mk_fundamentalAlcoveStabilizerEquivQuotient_symm_apply
    (q : Multiplicative
      (P.coweightLattice ⧸ (P.corootSpan ℤ).comap P.coweightLattice.subtype)) :
    Multiplicative.ofAdd (Submodule.Quotient.mk
      ⟨((P.fundamentalAlcoveStabilizerEquivQuotient b).symm q).1 0,
        (P.mem_extendedAffineWeylGroup_iff.1
          (P.fundamentalAlcoveStabilizer_le_extendedAffineWeylGroup b
            ((P.fundamentalAlcoveStabilizerEquivQuotient b).symm q).2)).2⟩) = q := by
  simpa only [fundamentalAlcoveStabilizerEquivQuotient_apply,
    fundamentalAlcoveStabilizerToQuotient_apply] using
    (P.fundamentalAlcoveStabilizerEquivQuotient b).apply_symm_apply q

end Field

end RootPairing
