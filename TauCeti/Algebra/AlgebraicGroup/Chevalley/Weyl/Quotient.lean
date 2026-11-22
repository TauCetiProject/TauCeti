/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Borel
import TauCeti.Algebra.AlgebraicGroup.Chevalley.Weyl.Word

/-!
# The Weyl quotient of Chevalley data

For every Chevalley datum of any valid Dynkin type (including `G₂`) over a nontrivial
commutative ring, the quotient of `weylSubgroup` by its actual character-lattice torus is
canonically isomorphic to the Weyl group of the pinned root datum. The equivalence sends the class
of each pinned simple Weyl representative to its simple reflection. Over a field, the kernel of
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

private def simpleLift (i : Fin t.rank) : N :=
  ⟨D.weylElement (t.simpleIndex ht i) A 1,
    D.weylElement_simpleIndex_one_mem_weylSubgroup A i⟩

private def residueHom [Nontrivial A] : N →* (t.simplyConnectedRootDatum ht).weylGroup :=
  let M := (Ideal.exists_maximal A).choose
  let _ : M.IsMaximal := (Ideal.exists_maximal A).choose_spec
  let _ := Ideal.Quotient.field M
  (D.weylProjection (A ⧸ M)).comp (D.weylSubgroupMap A (Ideal.Quotient.mk M))

private theorem residueHom_torusPoints [Nontrivial A] (s : Fin t.rank → Aˣ)
    (hx : D.torusPoints A s ∈ N) :
    D.residueHom A ⟨D.torusPoints A s, hx⟩ = 1 := by
  simp only [residueHom, MonoidHom.comp_apply, D.weylSubgroupMap_torusPoints,
    D.weylProjection_torusPoints]

private theorem residueHom_weylElement [Nontrivial A] (i : Fin t.rank) :
    D.residueHom A (D.simpleLift A i) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) := by
  simp only [residueHom, simpleLift, MonoidHom.comp_apply, D.weylSubgroupMap_weylElement,
    D.weylProjection_weylElement_simpleIndex_one]

private theorem residueHom_list_prod_simpleLift [Nontrivial A] (l : List (Fin t.rank)) :
    D.residueHom A (l.map (D.simpleLift A)).prod = t.geckWeylWordProd ht l := by
  induction l with
  | nil => simp only [List.map_nil, List.prod_nil, map_one, geckWeylWordProd_nil]
  | cons i l ih =>
    simp only [List.map_cons, List.prod_cons, map_mul, D.residueHom_weylElement A i, ih,
      geckWeylWordProd_cons]

private theorem residueHom_surjective [Nontrivial A] :
    Function.Surjective (D.residueHom A) := by
  intro w
  obtain ⟨l, rfl⟩ := t.geckWeylWordProd_surjective ht w
  exact ⟨(l.map (D.simpleLift A)).prod, D.residueHom_list_prod_simpleLift A l⟩

private theorem ker_residueHom [Nontrivial A] : (D.residueHom A).ker = H := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  constructor
  · intro hg
    obtain ⟨l, s, hls⟩ :=
      (D.mem_weylSubgroup_iff_exists_list_prod_mul_torusPoints A).mp g.property
    have hg_eq : g = (l.map (D.simpleLift A)).prod *
        ⟨D.torusPoints A s, D.torusPoints_mem_weylSubgroup A s⟩ := by
      apply Subtype.ext
      simpa only [Subgroup.coe_mul, Subgroup.val_list_prod, List.map_map, simpleLift,
        Function.comp_def] using hls.symm
    have hl : t.geckWeylWordProd ht l = 1 := by
      simpa only [hg_eq, map_mul, D.residueHom_list_prod_simpleLift, D.residueHom_torusPoints,
        mul_one] using hg
    obtain ⟨r, hr⟩ := D.weylWord_mem_range_torusPoints_of_geckWeylWordProd_eq_one A l hl
    refine ⟨r * s, ?_⟩
    rw [← hls, ← hr, (D.torusPoints A).map_mul]
  · rintro ⟨s, hs⟩
    have hg : g = ⟨D.torusPoints A s, D.torusPoints_mem_weylSubgroup A s⟩ := Subtype.ext hs.symm
    rw [hg, D.residueHom_torusPoints]

/-- Over any nontrivial commutative ring, the quotient of `D.weylSubgroup A` by the actual
torus `T_D(A)` is canonically isomorphic to the Weyl group of the pinned root datum. -/
def weylSubgroupQuotientMulEquiv [Nontrivial A] :
    Q ≃* (t.simplyConnectedRootDatum ht).weylGroup :=
  (QuotientGroup.quotientMulEquivOfEq (D.ker_residueHom A).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective (D.residueHom A) (D.residueHom_surjective A))

private theorem weylSubgroupQuotientMulEquiv_mk_apply [Nontrivial A] (g : N) :
    D.weylSubgroupQuotientMulEquiv A (QuotientGroup.mk g) = D.residueHom A g :=
  rfl

/-- The Weyl quotient equivalence sends the class of a pinned simple Weyl representative
to its simple reflection. -/
@[simp↓]
theorem weylSubgroupQuotientMulEquiv_mk_weylElement [Nontrivial A] (i : Fin t.rank) :
    D.weylSubgroupQuotientMulEquiv A
        (QuotientGroup.mk
          ⟨D.weylElement (t.simpleIndex ht i) A 1,
            D.weylElement_simpleIndex_one_mem_weylSubgroup A i⟩) =
      RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i) :=
  D.residueHom_weylElement A i

/-- The inverse Weyl quotient equivalence sends a pinned simple reflection to the class
of its pinned Weyl representative. -/
@[simp↓]
theorem weylSubgroupQuotientMulEquiv_symm_ofIdx [Nontrivial A] (i : Fin t.rank) :
    (D.weylSubgroupQuotientMulEquiv A).symm
        (RootPairing.weylGroup.ofIdx (t.simplyConnectedRootDatum ht) (t.simpleIndex ht i)) =
      QuotientGroup.mk
        ⟨D.weylElement (t.simpleIndex ht i) A 1,
          D.weylElement_simpleIndex_one_mem_weylSubgroup A i⟩ := by
  rw [MulEquiv.symm_apply_eq, D.weylSubgroupQuotientMulEquiv_mk_weylElement]

end

noncomputable section

variable {t : DynkinType} {ht : t.Valid} (D : ChevalleyDatum t ht)
variable (K : Type*) [Field K]

local notation "Nₖ" => D.weylSubgroup K
local notation "Hₖ" => Subgroup.subgroupOf (MonoidHom.range (D.torusPoints K)) Nₖ

private theorem closure_weylSubgroup_generators :
    Subgroup.closure ((D.weylSubgroup K).subtype ⁻¹'
      (Set.range (D.torusPoints K) ∪
        Set.range (fun i => D.weylElement (t.simpleIndex ht i) K 1))) = ⊤ := by
  rw [D.weylSubgroup_def]
  exact Subgroup.closure_preimage_eq_top _

private theorem residueHom_eq_weylProjection : D.residueHom K = D.weylProjection K := by
  apply MonoidHom.eq_of_eqOn_dense (D.closure_weylSubgroup_generators K)
  rintro ⟨x, hx⟩ (⟨s, rfl⟩ | ⟨i, rfl⟩)
  · simp only [D.residueHom_torusPoints, D.weylProjection_torusPoints]
  · exact (D.residueHom_weylElement K i).trans
      (D.weylProjection_weylElement_simpleIndex_one K i).symm

/-- Over every field, the kernel of `D.weylProjection K` is precisely the actual torus inside
`D.weylSubgroup K`. -/
@[simp]
theorem ker_weylProjection : (D.weylProjection K).ker = Hₖ := by
  rw [← D.residueHom_eq_weylProjection K, D.ker_residueHom K]

/-- `weylSubgroupQuotientMulEquiv` evaluates on the class of `n` as `D.weylProjection K n`. -/
@[simp]
theorem weylSubgroupQuotientMulEquiv_mk (g : Nₖ) :
    D.weylSubgroupQuotientMulEquiv K (QuotientGroup.mk g) = D.weylProjection K g :=
  DFunLike.congr_fun (D.residueHom_eq_weylProjection K) g

/-- The inverse Weyl quotient equivalence sends a Weyl projection to its quotient class. -/
@[simp]
theorem weylSubgroupQuotientMulEquiv_symm_weylProjection (g : Nₖ) :
    (D.weylSubgroupQuotientMulEquiv K).symm (D.weylProjection K g) =
      QuotientGroup.mk g := by
  rw [MulEquiv.symm_apply_eq, D.weylSubgroupQuotientMulEquiv_mk]

end

end TauCeti.DynkinType.ChevalleyDatum
