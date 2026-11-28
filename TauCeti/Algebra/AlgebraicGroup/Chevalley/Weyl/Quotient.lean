/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Borel
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Lift
public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Root
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Word

/-!
# The Weyl quotient of Chevalley data

For every Chevalley datum of any valid Dynkin type (including `G₂`) over a nontrivial
commutative ring, the quotient of `weylSubgroup` by its actual character-lattice torus is
canonically isomorphic to the Weyl group of the pinned root datum. The equivalence sends the class
of every Steinberg Weyl representative `n_γ(s)` to the reflection `s_γ`, and evaluates the
word-times-torus normal form of any Weyl-subgroup element as the corresponding Weyl-group word
product. Its inverse is the Coxeter lift `ChevalleyDatum.weylQuotientLift`
(`ChevalleyDatum.weylSubgroupQuotientMulEquiv_symm_apply`), which is therefore injective, and the
equivalence is compatible with scalar extension
(`ChevalleyDatum.weylSubgroupQuotientMulEquiv_mk_weylSubgroupMap`). Over a field, the kernel of
the native Weyl projection is exactly that torus, and the quotient equivalence agrees with the
descended Weyl projection.

The argument reduces to a residue field to construct the homomorphism on `weylSubgroup`, proves
surjectivity on words in the pinned simple Weyl representatives, and identifies the kernel with the
actual torus via strong-exchange word shortening (`Chevalley/Weyl/Word.lean`) after
decomposing any element of `weylSubgroup` as a positive Weyl word times a torus point
(`Chevalley/Weyl/Borel.lean`). Neither Coxeter braid presentations nor point-generation or
infinitude assumptions are needed; in particular, the result holds for all Dynkin types including
`G₂`, adjoint data, and finite fields.

## References

* R. Steinberg, *Lectures on Chevalley Groups*, Chapter 3, Lemmas 19 and 22, and Chapter 6.
* R. W. Carter, *Simple Groups of Lie Type*, §§6.4 and 7.2.
-/

public section

namespace TauCeti.DynkinType.ChevalleyDatum

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (A : Type*) [CommRing A]

local notation "N" => D.weylSubgroup A
local notation "H" => Subgroup.subgroupOf (MonoidHom.range (D.torusPoints A)) N
local notation "Q" => N ⧸ H

private def residueIdeal [Nontrivial A] : Ideal A :=
  (Ideal.exists_maximal A).choose

private instance residueIdeal_isMaximal [Nontrivial A] : (residueIdeal A).IsMaximal :=
  (Ideal.exists_maximal A).choose_spec

attribute [local instance] Ideal.Quotient.field

private def residueHom [Nontrivial A] : N →* (t.simplyConnectedRootDatum ht).weylGroup :=
  (D.weylProjection (A ⧸ residueIdeal A)).comp
    (D.weylSubgroupMap A (Ideal.Quotient.mk (residueIdeal A)))

private theorem residueHom_torusPoints [Nontrivial A] (s : Fin t.rank → Aˣ)
    (hx : D.torusPoints A s ∈ N) :
    D.residueHom A ⟨D.torusPoints A s, hx⟩ = 1 := by
  dsimp only [residueHom, MonoidHom.comp_apply]
  rw [D.weylSubgroupMap_torusPoints, D.weylProjection_torusPoints]

private theorem residueHom_simpleWeylLift [Nontrivial A] (i : Fin t.rank) :
    D.residueHom A (D.simpleWeylLift A i) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  dsimp only [residueHom, MonoidHom.comp_apply]
  rw [D.weylSubgroupMap_simpleWeylLift, D.weylProjection_simpleWeylLift]

private theorem residueHom_weylElement [Nontrivial A] (γ : Fin t.numRoots) (s : Aˣ) :
    D.residueHom A ⟨D.weylElement γ A s, D.weylElement_mem_weylSubgroup γ A s⟩ =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ := by
  dsimp only [residueHom, MonoidHom.comp_apply]
  rw [D.weylSubgroupMap_weylElement, D.weylProjection_weylElement]

private theorem residueHom_surjective [Nontrivial A] :
    Function.Surjective (D.residueHom A) := by
  intro w
  obtain ⟨l, rfl⟩ := t.simplyConnectedWeylWordProd_surjective ht w
  exact ⟨(l.map (D.simpleWeylLift A)).prod,
    D.map_list_prod_simpleWeylLift A (D.residueHom A) (D.residueHom_simpleWeylLift A) l⟩

private theorem ker_residueHom [Nontrivial A] : (D.residueHom A).ker = H := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  constructor
  · intro hg
    obtain ⟨l, s, hls⟩ :=
      (D.mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints A).mp g.property
    have hg_eq : g = (l.map (D.simpleWeylLift A)).prod *
        ⟨D.torusPoints A s, D.torusPoints_mem_weylSubgroup A s⟩ := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, D.coe_list_prod_simpleWeylLift] using hls.symm
    have hl : t.simplyConnectedWeylWordProd ht l = 1 := by
      simpa only [hg_eq, map_mul,
        D.map_list_prod_simpleWeylLift A (D.residueHom A) (D.residueHom_simpleWeylLift A),
        D.residueHom_torusPoints, mul_one] using hg
    obtain ⟨r, hr⟩ := D.weylWord_mem_range_torusPoints_of_simplyConnectedWeylWordProd_eq_one A l hl
    refine ⟨r * s, ?_⟩
    rw [← hls, ← hr, (D.torusPoints A).map_mul]
  · rintro ⟨s, hs⟩
    have hg : g = ⟨D.torusPoints A s, D.torusPoints_mem_weylSubgroup A s⟩ := Subtype.ext hs.symm
    rw [hg, D.residueHom_torusPoints]

/-- Over any nontrivial commutative ring, the quotient of `D.weylSubgroup A` by the actual
torus `T_D(A)` is canonically isomorphic to the Weyl group of the pinned root datum. -/
def weylSubgroupQuotientMulEquiv [Nontrivial A] :
    Q ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  QuotientGroup.liftEquiv H (D.residueHom_surjective A) (D.ker_residueHom A).symm

private theorem weylSubgroupQuotientMulEquiv_mk_apply [Nontrivial A] (g : N) :
    D.weylSubgroupQuotientMulEquiv A (QuotientGroup.mk g) = D.residueHom A g :=
  QuotientGroup.liftEquiv_mk H (D.residueHom_surjective A) (D.ker_residueHom A).symm g

/-- The Weyl quotient equivalence sends the class of a pinned simple Weyl lift to its simple
reflection. -/
@[simp]
theorem weylSubgroupQuotientMulEquiv_mk_simpleWeylLift [Nontrivial A] (i : Fin t.rank) :
    D.weylSubgroupQuotientMulEquiv A (QuotientGroup.mk (D.simpleWeylLift A i)) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  rw [D.weylSubgroupQuotientMulEquiv_mk_apply A, D.residueHom_simpleWeylLift A i]

/-- The Weyl quotient equivalence sends the class of Steinberg's Weyl element `n_γ(s)`
to the reflection `s_γ`. -/
@[simp↓]
theorem weylSubgroupQuotientMulEquiv_mk_weylElement [Nontrivial A]
    (γ : Fin t.numRoots) (s : Aˣ) :
    D.weylSubgroupQuotientMulEquiv A
        (QuotientGroup.mk ⟨D.weylElement γ A s, D.weylElement_mem_weylSubgroup γ A s⟩) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ := by
  rw [D.weylSubgroupQuotientMulEquiv_mk_apply A, D.residueHom_weylElement A γ s]

/-- The Weyl quotient equivalence sends a product of pinned simple Weyl lifts and an actual
torus point to the corresponding product of simple reflections in the Weyl group. -/
theorem weylSubgroupQuotientMulEquiv_mk_list_prod_simpleWeylLift_mul_torusPoints
    [Nontrivial A] (l : List (Fin t.rank)) (s : Fin t.rank → Aˣ) :
    D.weylSubgroupQuotientMulEquiv A
        (QuotientGroup.mk ((l.map (D.simpleWeylLift A)).prod *
          ⟨D.torusPoints A s, D.torusPoints_mem_weylSubgroup A s⟩)) =
      t.simplyConnectedWeylWordProd ht l := by
  rw [D.weylSubgroupQuotientMulEquiv_mk_apply A, map_mul,
    D.map_list_prod_simpleWeylLift A (D.residueHom A) (D.residueHom_simpleWeylLift A) l,
    D.residueHom_torusPoints A s, mul_one]

/-- The inverse Weyl quotient equivalence sends a root reflection `s_γ` to the class of
Steinberg's Weyl element `n_γ(1)`. -/
@[simp↓]
theorem weylSubgroupQuotientMulEquiv_symm_ofIdx [Nontrivial A] (γ : Fin t.numRoots) :
    (D.weylSubgroupQuotientMulEquiv A).symm
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) γ) =
      QuotientGroup.mk ⟨D.weylElement γ A 1, D.weylElement_mem_weylSubgroup γ A 1⟩ := by
  rw [MulEquiv.symm_apply_eq, D.weylSubgroupQuotientMulEquiv_mk_weylElement]

/-- The Weyl quotient equivalence is a left inverse of the Coxeter lift `weylQuotientLift`. -/
@[simp]
theorem weylSubgroupQuotientMulEquiv_weylQuotientLift [Nontrivial A]
    (w : (t.simplyConnectedRootDatum ht).weylGroup) :
    D.weylSubgroupQuotientMulEquiv A (D.weylQuotientLift A w) = w := by
  obtain ⟨l, rfl⟩ := t.simplyConnectedWeylWordProd_surjective ht w
  rw [D.weylQuotientLift_simplyConnectedWeylWordProd, ← D.list_prod_map_simpleWeylLift,
    D.weylSubgroupQuotientMulEquiv_mk_apply A,
    D.map_list_prod_simpleWeylLift A (D.residueHom A) (D.residueHom_simpleWeylLift A) l]

/-- Over a nontrivial commutative ring, the inverse of the Weyl quotient equivalence is the
Coxeter lift `weylQuotientLift`. -/
theorem weylSubgroupQuotientMulEquiv_symm_apply [Nontrivial A]
    (w : (t.simplyConnectedRootDatum ht).weylGroup) :
    (D.weylSubgroupQuotientMulEquiv A).symm w = D.weylQuotientLift A w := by
  rw [MulEquiv.symm_apply_eq, D.weylSubgroupQuotientMulEquiv_weylQuotientLift]

/-- Over any nontrivial commutative ring `A`, the Coxeter lift `weylQuotientLift` is injective. -/
theorem weylQuotientLift_injective [Nontrivial A] : Function.Injective (D.weylQuotientLift A) :=
  Function.LeftInverse.injective (D.weylSubgroupQuotientMulEquiv_weylQuotientLift A)

/-- Scalar extension along a ring homomorphism between nontrivial commutative rings commutes with
`weylSubgroupQuotientMulEquiv`. -/
@[simp]
theorem weylSubgroupQuotientMulEquiv_mk_weylSubgroupMap [Nontrivial A] {B : Type*} [CommRing B]
    [Nontrivial B] (f : A →+* B) (g : N) :
    D.weylSubgroupQuotientMulEquiv B (QuotientGroup.mk (D.weylSubgroupMap A f g)) =
      D.weylSubgroupQuotientMulEquiv A (QuotientGroup.mk g) := by
  refine DFunLike.congr_fun
    (MonoidHom.eq_of_eqOn_dense (D.closure_weylSubgroup_generators A) ?_ :
    (((D.weylSubgroupQuotientMulEquiv B).toMonoidHom.comp
      (QuotientGroup.mk' (((D.torusPoints B).range).subgroupOf (D.weylSubgroup B)))).comp
        (D.weylSubgroupMap A f)) =
      (D.weylSubgroupQuotientMulEquiv A).toMonoidHom.comp (QuotientGroup.mk' H)) g
  rintro ⟨x, hx⟩ (⟨s, rfl⟩ | ⟨i, rfl⟩)
  · simp only [MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      D.weylSubgroupMap_torusPoints, D.mk_torusPoints_eq_one, map_one]
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, QuotientGroup.mk'_apply]
    rw [D.mk_weylElement_eq_simpleWeylLift, D.weylSubgroupMap_simpleWeylLift,
      weylSubgroupQuotientMulEquiv_mk_simpleWeylLift,
      weylSubgroupQuotientMulEquiv_mk_simpleWeylLift]

end

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (K : Type*) [Field K]

local notation "Nₖ" => D.weylSubgroup K
local notation "Hₖ" => Subgroup.subgroupOf (MonoidHom.range (D.torusPoints K)) Nₖ

private theorem residueHom_eq_weylProjection : D.residueHom K = D.weylProjection K := by
  apply MonoidHom.eq_of_eqOn_dense (D.closure_weylSubgroup_generators K)
  rintro ⟨x, hx⟩ (⟨s, rfl⟩ | ⟨i, rfl⟩)
  · simp only [D.residueHom_torusPoints, D.weylProjection_torusPoints]
  · have hsub :
        (⟨D.weylElement (t.simpleIndex ht i) K 1, hx⟩ : D.weylSubgroup K) =
          D.simpleWeylLift K i :=
      Subtype.ext (D.coe_simpleWeylLift K i).symm
    rw [hsub]
    exact (D.residueHom_simpleWeylLift K i).trans (D.weylProjection_simpleWeylLift K i).symm

/-- Over every field, the kernel of `D.weylProjection K` is precisely the actual torus inside
`D.weylSubgroup K`. -/
@[simp]
theorem ker_weylProjection : (D.weylProjection K).ker = Hₖ := by
  rw [← D.residueHom_eq_weylProjection K, D.ker_residueHom K]

/-- A point of `N` has trivial Weyl projection exactly when it is a torus point. -/
theorem weylProjection_eq_one_iff_mem_range_torusPoints (g : Nₖ) :
    D.weylProjection K g = 1 ↔ (g : D.points K) ∈ (D.torusPoints K).range := by
  rw [← MonoidHom.mem_ker, ker_weylProjection, Subgroup.mem_subgroupOf]

/-- `weylSubgroupQuotientMulEquiv` evaluates on the class of `n` as `D.weylProjection K n`. -/
@[simp]
theorem weylSubgroupQuotientMulEquiv_mk (g : Nₖ) :
    D.weylSubgroupQuotientMulEquiv K (QuotientGroup.mk g) = D.weylProjection K g := by
  rw [D.weylSubgroupQuotientMulEquiv_mk_apply K g, D.residueHom_eq_weylProjection K]

/-- The inverse Weyl quotient equivalence sends a Weyl projection to its quotient class. -/
@[simp]
theorem weylSubgroupQuotientMulEquiv_symm_weylProjection (g : Nₖ) :
    (D.weylSubgroupQuotientMulEquiv K).symm (D.weylProjection K g) =
      QuotientGroup.mk g := by
  rw [MulEquiv.symm_apply_eq, D.weylSubgroupQuotientMulEquiv_mk]

/-- On a product of a Weyl word and an actual torus point, `D.weylProjection K` evaluates to the
Weyl-group element spelled by the word. -/
theorem weylProjection_list_prod_mul_torusPoints (l : List (Fin t.rank))
    (s : Fin t.rank → Kˣ) :
    D.weylProjection K
      ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod * D.torusPoints K s,
        mul_mem (D.list_prod_map_weylElement_mem_weylSubgroup K l)
          (D.torusPoints_mem_weylSubgroup K s)⟩ =
      t.simplyConnectedWeylWordProd ht l := by
  rw [← D.weylSubgroupQuotientMulEquiv_mk,
    ← D.weylSubgroupQuotientMulEquiv_mk_list_prod_simpleWeylLift_mul_torusPoints K l s,
    D.list_prod_map_simpleWeylLift K l]
  rfl

/-- On a product of simple Weyl elements `n_{αᵢ}(1)`, `D.weylProjection K` evaluates to the
Weyl-group element spelled by the word. -/
theorem weylProjection_list_prod (l : List (Fin t.rank)) :
    D.weylProjection K
      ⟨(l.map fun i => D.weylElement (t.simpleIndex ht i) K 1).prod,
        D.list_prod_map_weylElement_mem_weylSubgroup K l⟩ =
      t.simplyConnectedWeylWordProd ht l := by
  simpa only [map_one, mul_one] using D.weylProjection_list_prod_mul_torusPoints K l 1

end

end TauCeti.DynkinType.ChevalleyDatum
