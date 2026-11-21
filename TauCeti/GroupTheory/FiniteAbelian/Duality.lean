/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Abelianization.Finite
public import Mathlib.GroupTheory.FiniteAbelian.Duality
import TauCeti.GroupTheory.Coset.Fiber

/-!
# The character group of a finite group is the dual of its abelianization

A linear character of a group `G`, a homomorphism `G →* Mˣ` into the units of a commutative
monoid, kills every commutator, so it factors uniquely through the abelianization. Mathlib's
`Group.Abelianization.lift` is that bijection, and Mathlib's
`CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity` counts the characters of a finite *commutative*
group. Composing the two counts the characters of an arbitrary finite group:

`Nat.card (G →* Mˣ) = Nat.card (Group.Abelianization G)`.

The hypothesis is the one Mathlib's counting theorem carries, asked of the abelianization rather
than of `G`: writing `n` for `Monoid.exponent (Group.Abelianization G)`, `HasEnoughRootsOfUnity M n`
asks
that `M` contain a primitive `n`-th root of unity and that the `n`-th roots of unity in `M` form a
cyclic group. An algebraically closed field of characteristic zero satisfies it for every `n`. It is
a sufficient condition, not one shown here to be necessary, but some hypothesis on `M` is needed:
a character group can collapse for want of roots of unity — over `ℝ` the group `ZMod 3` has only the
trivial character, while its abelianization is itself — and it can also grow, since over `ℝ × ℝ`
the group `ZMod 2` has four characters rather than two.

In particular a finite group has a nontrivial linear character exactly when it is not perfect, and
a perfect group has none at all; the count is what turns a computation of the abelianization into a
complete list of linear characters.

## Main statements

* `TauCeti.card_monoidHom_eq_card_abelianization`: **the linear characters of a finite group are
  counted by its abelianization.**
* `CommGroup.card_monoidHom_not_le_ker`: for a finite commutative group `G` and a subgroup `H`,
  the characters of `G` that are nontrivial on `H` are `#G - #(G ⧸ H)` in number, since those
  trivial on `H` are the characters of `G ⧸ H` (Mathlib's `CommGroup.card_domRestrictHom_ker`).
* `CommGroup.finsum_domRestrictHom`: for a subgroup `H` of a finite commutative group `G`, a
  function of the restriction to `H`, summed over the characters of `G`, is `#(G ⧸ H)` times its
  sum over the characters of `H`.
* `CommGroup.exists_monoidHom_apply_eq`: evaluation at `a : G` maps the characters of `G`
  surjectively onto `rootsOfUnity (orderOf a) M`.
* `CommGroup.finprod_monoidHom_apply`: the product of `g (χ a)` over all characters of `G` is the
  product of `g ζ` over `rootsOfUnity (orderOf a) M`, raised to `#(G ⧸ Subgroup.zpowers a)`.
* `MonoidHom.exists_comp_eq_iff_ker_le_ker`: a character extends along a homomorphism into a
  finite commutative group exactly when it kills the kernel of that homomorphism. This is
  Mathlib's `MonoidHom.domRestrict_surjective` applied to the range of the homomorphism.

## References

* I. M. Isaacs, *Character Theory of Finite Groups*, AMS Chelsea (1976), Chapter 2, where the
  linear characters of `G` are identified with the characters of `G / G'`.
-/

public section

namespace TauCeti

/-- **The linear characters of a finite group are counted by its abelianization.** Every
homomorphism `G →* Mˣ` factors uniquely through `Group.Abelianization G`, and the characters of a
finite
commutative group with enough roots of unity in `M` are as many as its elements. -/
theorem card_monoidHom_eq_card_abelianization (G M : Type*) [Group G] [Finite G] [CommMonoid M]
    [HasEnoughRootsOfUnity M (Monoid.exponent (Group.Abelianization G))] :
    Nat.card (G →* Mˣ) = Nat.card (Group.Abelianization G) := by
  rw [← CommGroup.card_monoidHom_of_hasEnoughRootsOfUnity (Group.Abelianization G) M]
  exact Nat.card_congr Group.Abelianization.lift

end TauCeti

namespace CommGroup

variable {G : Type*} (M : Type*) [CommGroup G] [Finite G] [CommMonoid M]
  [HasEnoughRootsOfUnity M (Monoid.exponent G)]

/-- **The characters nontrivial on a subgroup.** If `M` has enough roots of unity, the
homomorphisms `G →* Mˣ` of a finite commutative group that are not trivial on a subgroup `H` are
`#G - #(G ⧸ H)` in number: those trivial on `H` are the characters of `G ⧸ H`. -/
theorem card_monoidHom_not_le_ker (H : Subgroup G) :
    Nat.card {φ : G →* Mˣ // ¬H ≤ φ.ker} = Nat.card G - Nat.card (G ⧸ H) := by
  classical
  have := Fintype.ofFinite (G →* Mˣ)
  have hle : Nat.card {φ : G →* Mˣ // H ≤ φ.ker} = Nat.card (G ⧸ H) := by
    rw [← card_domRestrictHom_ker M H]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun φ ↦ by simp [IsConcreteLE.le_iff])
  rw [← card_monoidHom_of_hasEnoughRootsOfUnity G M, ← hle, Nat.card_eq_fintype_card,
    Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, Fintype.card_subtype_compl]

/-- **Summing over characters through a restriction.** If `M` has enough roots of unity, every
character of a subgroup `H` of a finite commutative group `G` extends to exactly `#(G ⧸ H)`
characters of `G`. So a function `g` of the restriction to `H`, summed over the characters of `G`,
is `#(G ⧸ H)` times its sum over the characters of `H`. -/
theorem finsum_domRestrictHom {N : Type*} [AddCommMonoid N] (H : Subgroup G)
    (g : (H →* Mˣ) → N) :
    ∑ᶠ χ : G →* Mˣ, g (MonoidHom.domRestrictHom H Mˣ χ) =
      Nat.card (G ⧸ H) • ∑ᶠ ψ : H →* Mˣ, g ψ := by
  have : HasEnoughRootsOfUnity M (Monoid.exponent H) :=
    HasEnoughRootsOfUnity.of_dvd M (Monoid.exponent_submonoid_dvd H.toSubmonoid)
  have := Fintype.ofFinite (G →* Mˣ)
  have := Fintype.ofFinite (H →* Mˣ)
  -- Restriction is surjective, so each fibre is a coset of its kernel, of order `#(G ⧸ H)`.
  rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, ← card_domRestrictHom_ker M H]
  -- Apply the multiplicative fibre-counting formula in `Multiplicative N` and transport it back.
  simpa only [Function.comp_apply, toAdd_prod, toAdd_pow, toAdd_ofAdd] using
    congrArg Multiplicative.toAdd <| MonoidHom.prod_comp_of_surjective _
      (MonoidHom.domRestrict_surjective M H) (Multiplicative.ofAdd ∘ g)

/-- Evaluation of a character at `a : G`, valued in the `(orderOf a)`-th roots of unity. -/
private def evalRootsOfUnityHom (a : G) : (G →* Mˣ) →* rootsOfUnity (orderOf a) M where
  toFun χ := ⟨χ a, (mem_rootsOfUnity (orderOf a) (χ a)).mpr <| by
    rw [← map_pow, pow_orderOf_eq_one, map_one]⟩
  map_one' := Subtype.ext (MonoidHom.one_apply a)
  map_mul' χ ψ := Subtype.ext (MonoidHom.mul_apply χ ψ a)

omit [Finite G] [HasEnoughRootsOfUnity M (Monoid.exponent G)] in
/-- The kernel of evaluation at `a` is the kernel of restriction to `Subgroup.zpowers a`. -/
private theorem ker_evalRootsOfUnityHom (a : G) :
    (evalRootsOfUnityHom M a).ker = (MonoidHom.domRestrictHom (Subgroup.zpowers a) Mˣ).ker := by
  ext χ
  simp only [MonoidHom.mem_ker, evalRootsOfUnityHom, MonoidHom.coe_mk, OneHom.coe_mk,
    Subtype.ext_iff, OneMemClass.coe_one, MonoidHom.domRestrictHom_apply, MonoidHom.ext_iff,
    MonoidHom.domRestrict_apply, MonoidHom.one_apply]
  refine ⟨fun h ⟨x, hx⟩ ↦ ?_, fun h ↦ h ⟨a, Subgroup.mem_zpowers a⟩⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
  rw [map_zpow, h, one_zpow]

/-- Evaluation at `a : G` maps `G →* Mˣ` surjectively onto `rootsOfUnity (orderOf a) M`. -/
private theorem surjective_evalRootsOfUnityHom (a : G) :
    Function.Surjective (evalRootsOfUnityHom M a) := by
  have : NeZero (orderOf a) := ⟨(orderOf_pos a).ne'⟩
  have : HasEnoughRootsOfUnity M (orderOf a) :=
    HasEnoughRootsOfUnity.of_dvd M (Monoid.order_dvd_exponent a)
  refine MonoidHom.surjective_of_card_ker_le_div _ (le_of_eq ?_)
  rw [card_monoidHom_of_hasEnoughRootsOfUnity G M, HasEnoughRootsOfUnity.natCard_rootsOfUnity,
    ker_evalRootsOfUnityHom, card_domRestrictHom_ker,
    (Subgroup.zpowers a).card_eq_card_quotient_mul_card_subgroup, Nat.card_zpowers,
    Nat.mul_div_cancel _ (orderOf_pos a)]

/-- **Every `(orderOf a)`-th root of unity is attained by a character at `a`.** If `M` has enough
roots of unity for the finite commutative group `G`, then for any `a : G` and any
`ζ ∈ rootsOfUnity (orderOf a) M`, there exists `χ : G →* Mˣ` with `χ a = ζ`. -/
theorem exists_monoidHom_apply_eq (a : G) (ζ : rootsOfUnity (orderOf a) M) :
    ∃ χ : G →* Mˣ, χ a = ζ := by
  obtain ⟨χ, hχ⟩ := surjective_evalRootsOfUnityHom M a ζ
  exact ⟨χ, congrArg Subtype.val hχ⟩

/-- **Products over characters through evaluation at an element.** If `M` has enough roots of unity,
evaluation at `a : G` maps `G →* Mˣ` surjectively onto `rootsOfUnity (orderOf a) M` with fibers of
size `#(G ⧸ Subgroup.zpowers a)`. So the product of `g (χ a)` over all characters of `G` is the
product of `g ζ` over `rootsOfUnity (orderOf a) M`, raised to `#(G ⧸ Subgroup.zpowers a)`. -/
theorem finprod_monoidHom_apply {N : Type*} [CommMonoid N] (a : G) (g : Mˣ → N) :
    ∏ᶠ χ : G →* Mˣ, g (χ a) =
      (∏ᶠ ζ : rootsOfUnity (orderOf a) M, g ζ) ^ Nat.card (G ⧸ Subgroup.zpowers a) := by
  have : NeZero (orderOf a) := ⟨(orderOf_pos a).ne'⟩
  have : HasEnoughRootsOfUnity M (orderOf a) :=
    HasEnoughRootsOfUnity.of_dvd M (Monoid.order_dvd_exponent a)
  have := Fintype.ofFinite (G →* Mˣ)
  have := Fintype.ofFinite (rootsOfUnity (orderOf a) M)
  rw [finprod_eq_prod_of_fintype, finprod_eq_prod_of_fintype, ← card_domRestrictHom_ker M
    (Subgroup.zpowers a), ← ker_evalRootsOfUnityHom]
  exact MonoidHom.prod_comp_of_surjective (evalRootsOfUnityHom M a)
    (surjective_evalRootsOfUnityHom M a) (fun ζ ↦ g ζ)

end CommGroup

namespace MonoidHom

variable {A B R : Type*} [Group B] [CommMonoid R]

/-- A character extends along a homomorphism into a finite commutative group exactly when it kills
the kernel of that homomorphism. -/
theorem exists_comp_eq_iff_ker_le_ker [CommGroup A] [Finite A]
    [HasEnoughRootsOfUnity R (Monoid.exponent A)] (f : B →* A) (χ : B →* Rˣ) :
    (∃ ψ : A →* Rˣ, ψ.comp f = χ) ↔ f.ker ≤ χ.ker := by
  constructor
  · rintro ⟨ψ, rfl⟩
    rw [← comap_ker]
    exact f.ker_le_comap _
  · intro hχ
    obtain ⟨ψ, hψ⟩ := domRestrict_surjective (M := R) _
      (f.rangeRestrict.liftOfSurjective f.rangeRestrict_surjective ⟨χ, by rwa [ker_rangeRestrict]⟩)
    refine ⟨ψ, MonoidHom.ext fun b ↦ ?_⟩
    simpa using DFunLike.congr_fun hψ (f.rangeRestrict b)

end MonoidHom
