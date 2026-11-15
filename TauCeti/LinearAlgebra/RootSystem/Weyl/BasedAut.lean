/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.LinearAlgebra.RootSystem.CartanMatrix
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Chamber
public import TauCeti.LinearAlgebra.RootSystem.Weyl.Transport
import TauCeti.LinearAlgebra.RootSystem.Isomorphism
import TauCeti.LinearAlgebra.RootSystem.Weyl.Automorphism

/-!
# The Weyl group complements the stabilizer of a base

Let `P` be a finite reduced crystallographic root pairing over a characteristic-zero domain, and
let `b` be a base. The automorphisms of `P` that carry the simple roots of `b` onto themselves
form a subgroup `b.basedAut` of the automorphism group `P.Aut`. This file proves that the Weyl
group is a complement of that subgroup, so that every automorphism `g` factors uniquely as
`g = w δ` with `w` in the Weyl group and `δ` fixing `b`. Since the Weyl group is normal
(`RootPairing.weylGroup_normal`), this is a semidirect product decomposition
`Aut(P) ≃ W ⋊ Aut(P, b)`, with `Aut(P, b)` acting on `W` by conjugation.

The proof is the classical one. The automorphism `g` carries `b` to a base `b.map g`, and the Weyl
group acts simply transitively on the bases (`RootPairing.Base.existsUnique_map_eq`): there is
exactly one `w` in the Weyl group with `b.map w = b.map g`, and then `w⁻¹ g` fixes `b`. Applied to
the base `b` itself, uniqueness says that the only Weyl-group element fixing `b` is the identity.

Neither spanning nor an order on the coefficients is assumed, so the theorem applies to root
data, that is, to root pairings over `ℤ`, with arbitrary character and cocharacter lattices.

The subgroup `b.basedAut` is described in three equivalent ways: as the setwise stabilizer of the
simple roots (its definition), as the stabilizer of the base (`b.map g = b`), and, for finite
crystallographic pairings over a characteristic-zero domain, as the stabilizer of the set of
positive roots. Over a linearly ordered coefficient ring it is also the stabilizer of the open
dominant chamber.

For a root system (roots and coroots both spanning), every permutation of the simple roots
preserving the Cartan matrix extends uniquely to a based automorphism
(`RootPairing.Base.existsUnique_basedAut_of_cartanMatrix`).

## Main definitions

* `RootPairing.Base.basedAut`: the automorphisms of a root pairing carrying the simple roots of a
  base onto themselves.
* `RootPairing.Base.conjWeylGroup`: the action of the based automorphisms on the Weyl group by
  conjugation, `δ • w = δ w δ⁻¹` (`RootPairing.Base.coe_conjWeylGroup_apply`).
* `RootPairing.Base.semidirectProductMulEquiv`: the multiplicative equivalence
  `W ⋊ Aut(P, b) ≃* Aut(P)`, sending `(w, δ)` to `w δ`.

## Main results

* `RootPairing.Base.mem_basedAut_iff`, `RootPairing.Base.mem_basedAut_iff_forall_mem_support`
  and `RootPairing.Base.mem_basedAut_iff_map_eq`: an automorphism is based exactly when it carries
  the simple roots onto, or into, themselves, and exactly when it fixes the base.
* `RootPairing.Base.mem_basedAut_iff_image_posRoots`: an automorphism is based exactly when it
  carries the positive roots onto themselves.
* `RootPairing.Base.mem_basedAut_iff_smul_openDominantChamber`: over a linearly ordered
  coefficient ring, an automorphism is based exactly when it preserves the open dominant chamber.
* `RootPairing.Base.isComplement'_weylGroup_basedAut`: **the Weyl group complements the based
  automorphisms**.
* `RootPairing.Base.existsUnique_basedAut_of_cartanMatrix`: for a root system, each symmetry of
  the Cartan matrix extends uniquely to a based automorphism.
* `RootPairing.Base.coe_mul_left`: the product formula `(w, δ) (v, η) = (w δ v δ⁻¹, δ η)` in the
  semidirect product.
* `RootPairing.Base.semidirectProductMulEquiv_symm_mul` and
  `RootPairing.Base.coe_semidirectProductMulEquiv_symm_right`: the factors of `w δ` are `w` and
  `δ`, and the based factor of `g` is `w⁻¹ g` for its Weyl factor `w`.
* `RootPairing.Base.root_indexEquiv_semidirectProductMulEquiv` and
  `RootPairing.Base.coroot'_indexEquiv_semidirectProductMulEquiv`: the roots and coroots are
  transported by the based factor and then by the Weyl factor.
* `RootPairing.Base.map_semidirectProductMulEquiv` and
  `RootPairing.Base.map_semidirectProductMulEquiv_symm_left`: the Weyl factor of an automorphism
  `g` is the Weyl-group element carrying `b` to `b.map g`.

## References

* M. Demazure, A. Grothendieck (eds.), *Schémas en groupes III* (SGA 3), Exposé XXI, Lemma 6.7.1
  and Proposition 6.7.2.
* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Ch. VI, §1.5, Proposition 16.
* J. S. Milne, *Algebraic Groups*, Cambridge Studies in Advanced Mathematics 170, Appendix C,
  Proposition C.53.
-/

public section

open Pointwise Set TauCeti

namespace RootPairing.Base

variable {ι R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  {P : RootPairing ι R M N}

/-- The **based automorphisms** of a base `b`: the automorphisms of the root pairing whose action
on the root indices carries the simple roots of `b` onto themselves. This is the inverse image of
the setwise stabilizer of `b.support` under the permutation representation on root indices. -/
noncomputable def basedAut (b : P.Base) : Subgroup P.Aut :=
  (MulAction.stabilizer (Equiv.Perm ι) (b.support : Set ι)).comap (Equiv.indexHom P)

variable {b : P.Base} {g : P.Aut}

/-- An automorphism is based exactly when its action on root indices carries the simple roots onto
themselves. -/
@[simp]
theorem mem_basedAut_iff : g ∈ b.basedAut ↔ g.indexEquiv '' b.support = b.support := by
  simp only [basedAut, Subgroup.mem_comap, MulAction.mem_stabilizer_iff, ← Set.image_smul,
    Equiv.Perm.smul_def, Equiv.indexHom_apply]

/-- **An automorphism is based exactly when it fixes the base.** -/
theorem mem_basedAut_iff_map_eq : g ∈ b.basedAut ↔ b.map g = b := by
  classical
  rw [mem_basedAut_iff, Base.ext_iff, support_map_eq, ← Finset.coe_inj, Finset.coe_image]

/-- A based automorphism fixes the base. -/
theorem map_eq_of_mem_basedAut (h : g ∈ b.basedAut) : b.map g = b :=
  mem_basedAut_iff_map_eq.mp h

/-- An automorphism is based exactly when it carries every simple root to a simple root. -/
theorem mem_basedAut_iff_forall_mem_support :
    g ∈ b.basedAut ↔ ∀ i ∈ b.support, g.indexEquiv i ∈ b.support := by
  refine ⟨fun h i hi ↦ ?_, fun h ↦ mem_basedAut_iff_map_eq.mpr (map_eq_of_forall_mem_support h)⟩
  rw [← Finset.mem_coe, ← mem_basedAut_iff.mp h]
  exact Set.mem_image_of_mem _ hi

/-- A based automorphism carries the positive roots onto themselves. -/
theorem image_posRoots_of_mem_basedAut [CharZero R] (h : g ∈ b.basedAut) :
    g.indexEquiv '' posRoots P b = posRoots P b := by
  rw [← posRoots_map, map_eq_of_mem_basedAut h]

/-- **An automorphism is based exactly when it carries the positive roots onto themselves.** -/
theorem mem_basedAut_iff_image_posRoots [CharZero R] [Finite ι] [IsDomain R]
    [P.IsCrystallographic] :
    g ∈ b.basedAut ↔ g.indexEquiv '' posRoots P b = posRoots P b := by
  refine ⟨image_posRoots_of_mem_basedAut, fun h ↦ ?_⟩
  -- The identity of the Weyl group matches the positive roots of `b` and of `b.map g`.
  have hb : b.map ((1 : P.weylGroup) : P.Aut) = b.map g := by
    refine (map_eq_iff_mapsTo_posRoots (w := 1)).mpr fun i hi ↦ ?_
    rw [posRoots_map, h]
    simpa using hi
  rw [mem_basedAut_iff_map_eq, ← hb, OneMemClass.coe_one, Base.map_one]

section Chamber

/-- A based automorphism preserves the open dominant chamber. -/
theorem smul_openDominantChamber_of_mem_basedAut [Preorder R] (h : g ∈ b.basedAut) :
    g • openDominantChamber P b = openDominantChamber P b := by
  rw [smul_openDominantChamber, map_eq_of_mem_basedAut h]

/-- **An automorphism is based exactly when it preserves the open dominant chamber**, over a
linearly ordered coefficient ring. -/
theorem mem_basedAut_iff_smul_openDominantChamber [LinearOrder R] [IsStrictOrderedRing R]
    [Finite ι] [P.IsCrystallographic] [P.IsReduced] [P.flip.IsReduced] :
    g ∈ b.basedAut ↔ g • openDominantChamber P b = openDominantChamber P b := by
  refine ⟨smul_openDominantChamber_of_mem_basedAut, fun h ↦ ?_⟩
  -- The Weyl-group element `w` carrying `b` to `b.map g` preserves the open dominant chamber, so
  -- it is the identity.
  obtain ⟨w, hw, -⟩ := b.existsUnique_map_eq (b.map g)
  have hwC : w • openWeylChamber P b 1 = openWeylChamber P b 1 := by
    -- A Weyl-group element acts on sets of weights through its coercion to `P.Aut`, by definition
    -- of the subgroup action.
    change (w : P.Aut) • openWeylChamber P b 1 = openWeylChamber P b 1
    rw [openWeylChamber_one, smul_openDominantChamber, hw, ← smul_openDominantChamber, h]
  obtain rfl := eq_one_of_smul_openWeylChamber_eq P b hwC
  rw [mem_basedAut_iff_map_eq, ← hw, OneMemClass.coe_one, Base.map_one]

end Chamber

section Conj

/-- The action of the based automorphisms on the normal subgroup `W` by conjugation, the action
defining the semidirect product `RootPairing.Base.semidirectProductMulEquiv`. -/
noncomputable def conjWeylGroup (b : P.Base) : b.basedAut →* MulAut P.weylGroup :=
  P.weylGroup.normalizerMonoidHom.comp
    (Subgroup.inclusion (P.weylGroup.normalizer_eq_top ▸ le_top))

/-- A based automorphism `δ` acts on the Weyl group by `w ↦ δ w δ⁻¹`. -/
@[simp]
theorem coe_conjWeylGroup_apply (δ : b.basedAut) (w : P.weylGroup) :
    (b.conjWeylGroup δ w : P.Aut) = δ * w * (δ : P.Aut)⁻¹ := by
  rw [conjWeylGroup]
  rfl

/-- **The product formula of the semidirect product**: `(w, δ) (v, η)` has Weyl factor
`w δ v δ⁻¹`, and based factor `δ η` by `SemidirectProduct.mul_right`. -/
theorem coe_mul_left (x y : P.weylGroup ⋊[b.conjWeylGroup] b.basedAut) :
    ((x * y).left : P.Aut) = x.left * (x.right * y.left * (x.right : P.Aut)⁻¹) := by
  rw [SemidirectProduct.mul_left, Subgroup.coe_mul, coe_conjWeylGroup_apply]

end Conj

variable [Finite ι] [CharZero R] [IsDomain R] [P.IsCrystallographic] [P.IsReduced]

/-- **The Weyl group complements the based automorphisms**: every automorphism of a finite reduced
crystallographic root pairing over a characteristic-zero domain is uniquely the product `w δ` of
an element `w` of the Weyl group and a based automorphism `δ`. -/
theorem isComplement'_weylGroup_basedAut (b : P.Base) :
    P.weylGroup.IsComplement' b.basedAut := by
  refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
  · -- A Weyl-group element fixing `b` is the identity, by uniqueness in simple transitivity.
    refine Subgroup.disjoint_def.mpr fun {g} hw hb ↦ ?_
    obtain ⟨_, -, huniq⟩ := b.existsUnique_map_eq b
    have h₁ : (⟨g, hw⟩ : P.weylGroup) = 1 :=
      (huniq _ (map_eq_of_mem_basedAut hb)).trans (huniq 1 (by simp)).symm
    exact congrArg Subtype.val h₁
  · -- The Weyl-group element `w` carrying `b` to `b.map g` leaves the based factor `w⁻¹ g`.
    refine Set.eq_univ_of_forall fun g ↦ ?_
    obtain ⟨w, hw, -⟩ := b.existsUnique_map_eq (b.map g)
    refine Set.mem_mul.mpr ⟨w, w.2, (w : P.Aut)⁻¹ * g, ?_, mul_inv_cancel_left _ _⟩
    rw [SetLike.mem_coe, mem_basedAut_iff_map_eq, Base.map_mul, ← hw, ← Base.map_mul,
      inv_mul_cancel, Base.map_one]

/-- **Every symmetry of the Cartan matrix extends uniquely to a based automorphism.** For a finite
reduced crystallographic root system over a characteristic-zero domain, every permutation `σ` of
the simple roots of `b` preserving the Cartan matrix is the action on the simple roots of exactly
one based automorphism. -/
theorem existsUnique_basedAut_of_cartanMatrix [P.IsRootSystem] (b : P.Base)
    (σ : Equiv.Perm b.support) (hσ : ∀ i j, b.cartanMatrix (σ i) (σ j) = b.cartanMatrix i j) :
    ∃! g : b.basedAut, ∀ i : b.support, (g : P.Aut).indexEquiv i = σ i := by
  -- Existence: the automorphism built from the Cartan-matrix symmetry fixes `b`.
  let e : P.Aut := b.equivOfCartanMatrixEq b σ hσ
  have he (i : b.support) : e.indexEquiv i = σ i :=
    equivOfCartanMatrixEq_indexEquiv_apply b b σ hσ i
  refine ⟨⟨e, mem_basedAut_iff_map_eq.mpr (map_equivOfCartanMatrixEq b b σ hσ)⟩, he, ?_⟩
  -- Uniqueness: two such automorphisms differ by one fixing every simple root, the identity.
  rintro ⟨g, _⟩ hg
  have h : e⁻¹ * g = 1 := b.eq_one_of_forall_indexEquiv_eq fun i hi ↦ by
    have hgi : g.indexEquiv i = e.indexEquiv i := (hg ⟨i, hi⟩).trans (he ⟨i, hi⟩).symm
    simp [hgi]
  exact Subtype.ext (inv_mul_eq_one.mp h).symm

/-- **The automorphism group is the semidirect product of the Weyl group and the based
automorphisms**, the based automorphisms acting on the normal subgroup `W` by conjugation. The
equivalence sends `(w, δ)` to `w δ`. -/
noncomputable def semidirectProductMulEquiv (b : P.Base) :
    P.weylGroup ⋊[b.conjWeylGroup] b.basedAut ≃* P.Aut :=
  SemidirectProduct.mulEquivSubgroup (isComplement'_weylGroup_basedAut b)

/-- The equivalence `W ⋊ Aut(P, b) ≃* Aut(P)` multiplies the two factors. -/
@[simp]
theorem semidirectProductMulEquiv_apply (b : P.Base) (x) :
    b.semidirectProductMulEquiv x = (x.left : P.Aut) * x.right :=
  SemidirectProduct.mulEquivSubgroup_apply _ x

/-- The inverse equivalence splits an automorphism as the product of its two factors. -/
theorem semidirectProductMulEquiv_symm_left_mul_right (b : P.Base) (g : P.Aut) :
    ((b.semidirectProductMulEquiv.symm g).left : P.Aut) * (b.semidirectProductMulEquiv.symm g).right
      = g := by
  rw [← semidirectProductMulEquiv_apply, MulEquiv.apply_symm_apply]

/-- **The factors of `w δ` are `w` and `δ`**: the decomposition into a Weyl-group element and a
based automorphism is unique.

Not a `simp` lemma: `RootPairing.Equiv.mul_eq_comp` rewrites the product `w δ` in `P.Aut`
first. -/
theorem semidirectProductMulEquiv_symm_mul (w : P.weylGroup) (δ : b.basedAut) :
    b.semidirectProductMulEquiv.symm ((w : P.Aut) * δ) = ⟨w, δ⟩ := by
  rw [MulEquiv.symm_apply_eq, semidirectProductMulEquiv_apply]

/-- The based factor of an automorphism `g` is `w⁻¹ g`, for `w` its Weyl factor. -/
theorem coe_semidirectProductMulEquiv_symm_right (b : P.Base) (g : P.Aut) :
    ((b.semidirectProductMulEquiv.symm g).right : P.Aut) =
      ((b.semidirectProductMulEquiv.symm g).left : P.Aut)⁻¹ * g :=
  eq_inv_mul_of_mul_eq (semidirectProductMulEquiv_symm_left_mul_right b g)

/-- **Roots are transported by the based factor, then by the Weyl factor.** -/
theorem root_indexEquiv_semidirectProductMulEquiv (b : P.Base) (x) (i : ι) :
    P.root ((b.semidirectProductMulEquiv x).indexEquiv i) =
      (x.left : P.Aut) • (x.right : P.Aut) • P.root i := by
  rw [Equiv.root_indexEquiv_eq_smul, semidirectProductMulEquiv_apply, mul_smul]

/-- **Coroots are transported by the based factor, then by the Weyl factor**: the coroot of the
image root pairs with the image weight as the original coroot pairs with the original weight. -/
theorem coroot'_indexEquiv_semidirectProductMulEquiv (b : P.Base) (x) (i : ι) (y : M) :
    P.coroot' ((b.semidirectProductMulEquiv x).indexEquiv i)
      ((x.left : P.Aut) • (x.right : P.Aut) • y) = P.coroot' i y := by
  rw [← mul_smul, ← semidirectProductMulEquiv_apply, coroot'_smul, _root_.Equiv.symm_apply_apply]

/-- **The equivalence changes the base through its Weyl factor alone**: the based factor fixes
`b`. -/
theorem map_semidirectProductMulEquiv (b : P.Base) (x) :
    b.map (b.semidirectProductMulEquiv x) = b.map (x.left : P.Aut) := by
  rw [semidirectProductMulEquiv_apply, Base.map_mul, map_eq_of_mem_basedAut x.right.2]

/-- **The Weyl factor of an automorphism `g` carries `b` to `b.map g`**; by simple transitivity
it is the unique Weyl-group element doing so. -/
theorem map_semidirectProductMulEquiv_symm_left (b : P.Base) (g : P.Aut) :
    b.map ((b.semidirectProductMulEquiv.symm g).left : P.Aut) = b.map g := by
  rw [← map_semidirectProductMulEquiv, MulEquiv.apply_symm_apply]

end RootPairing.Base
