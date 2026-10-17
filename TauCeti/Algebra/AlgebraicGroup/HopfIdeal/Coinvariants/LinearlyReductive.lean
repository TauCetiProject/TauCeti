/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Coinvariants.Quotient
public import TauCeti.Algebra.AlgebraicGroup.LinearlyReductive
public import TauCeti.Algebra.AlgebraicGroup.Representation.Normal.Invariants
public import TauCeti.Algebra.Coalgebra.Comodule.OfCorestrict
public import TauCeti.Algebra.Coalgebra.Subcomodule.Induced
import TauCeti.Algebra.Coalgebra.Comodule.LinearlyReductive.Exact

/-!
# Extensions of linearly reductive groups

Let `G` be an affine group over a field `k` with coordinate Hopf algebra `H`, and let `N` be the
normal closed subgroup cut out by a normal Hopf ideal `I`. The quotient `G ⧸ N` has coordinate
Hopf algebra the coinvariants `H^{co H/I}` (`TauCeti.CommHopfAlgCat.coinvariants`).

For a representation `V` of `G`, the `N`-invariant vectors `V^N` form a subrepresentation
(`TauCeti.HopfIdeal.IsNormal.weightSpaceOneSubcomodule`) whose matrix coefficients are
`N`-invariant functions. So `V^N` is a representation of `G ⧸ N`, and its invariant vectors are
exactly the `G`-invariant vectors of `V`. Taking `G`-invariants is therefore taking `N`-invariants
and then `G ⧸ N`-invariants. Since a group is linearly reductive exactly when taking invariants
preserves surjections, an extension of linearly reductive groups is linearly reductive.

Together with `TauCeti.linearlyReductiveCommHopfAlgProperty.of_injective`, applied to the
projection `G → G ⧸ N`, this shows that when `N` is linearly reductive, `G` is linearly reductive
exactly when `G ⧸ N` is. No smoothness, finite-type, connectedness, or characteristic hypothesis is
needed.

## Main declarations

* `TauCeti.linearlyReductiveCommHopfAlgProperty.of_quotient_of_coinvariants`: if `N` and `G ⧸ N`
  are linearly reductive, then so is `G`.
* `TauCeti.linearlyReductiveCommHopfAlgProperty_iff_coinvariants`: for a linearly reductive
  normal subgroup `N`, the group `G` is linearly reductive exactly when `G ⧸ N` is.

## References

* J. S. Milne, *Algebraic Groups* (2017), Chapter 12.
* J. C. Jantzen, *Representations of Algebraic Groups*, I.6.
* W. C. Waterhouse, *Introduction to Affine Group Schemes*, §16.3.
-/

public section

open CategoryTheory
open scoped TensorProduct

namespace TauCeti

universe u v w

noncomputable section

variable {k : Type u} [Field k] {H : _root_.CommHopfAlgCat.{v} k} {I : HopfIdeal k H}
variable (V : Type w) [AddCommMonoid V] [Module k V] [Comodule k H V]

-- `CommHopfAlgCat.coinvariants` unfolds to a subalgebra, whose Hopf structure is not an instance.
private noncomputable abbrev coinvariantsHopfAlgebra (hI : I.IsNormal) :
    HopfAlgebra k (CommHopfAlgCat.coinvariants hI) :=
  (CommHopfAlgCat.coinvariants hI).hopfAlgebra

attribute [local instance] coinvariantsHopfAlgebra

/-- The inclusion of the coordinate ring of `G ⧸ N` as a coalgebra morphism. -/
private abbrev coinvariantsCoalgHom (hI : I.IsNormal) :
    CommHopfAlgCat.coinvariants hI →ₗc[k] H :=
  (CommHopfAlgCat.coinvariantsι hI).hom.toCoalgHom

private theorem lTensor_coinvariantsCoalgHom_injective (hI : I.IsNormal) (W : Type w)
    [AddCommMonoid W] [Module k W] :
    Function.Injective ((coinvariantsCoalgHom hI).toLinearMap.lTensor W) :=
  let _ : AddCommGroup W := Module.addCommMonoidToAddCommGroup k
  Module.Flat.lTensor_preserves_injective_linearMap (coinvariantsCoalgHom hI).toLinearMap
    (CommHopfAlgCat.hopfSubalgebraι_injective hI.isHopfSubalgebra_coinvariants)

private theorem lTensor_map_coinvariantsCoalgHom_injective (hI : I.IsNormal) (W : Type w)
    [AddCommMonoid W] [Module k W] :
    Function.Injective ((TensorProduct.map (coinvariantsCoalgHom hI).toLinearMap
      (coinvariantsCoalgHom hI).toLinearMap).lTensor W) :=
  let _ : AddCommGroup W := Module.addCommMonoidToAddCommGroup k
  have hι := CommHopfAlgCat.hopfSubalgebraι_injective hI.isHopfSubalgebra_coinvariants
  Module.Flat.lTensor_preserves_injective_linearMap _
    (TensorProduct.map_injective_of_flat_flat (coinvariantsCoalgHom hI).toLinearMap
      (coinvariantsCoalgHom hI).toLinearMap hι hι)

/-- The coaction on `N`-invariant vectors takes values in the coinvariants. -/
private theorem coact_mem_range_lTensor_coinvariantsCoalgHom (hI : I.IsNormal)
    (w : hI.weightSpaceOneSubcomodule V) :
    Comodule.coact (R := k) (C := H) w ∈
      LinearMap.range ((coinvariantsCoalgHom hI).toLinearMap.lTensor _) := by
  obtain ⟨z, hz⟩ := hI.coact_mem_range_lTensor_coinvariants w
  let e : Subalgebra.toSubmodule I.coinvariants →ₗ[k] CommHopfAlgCat.coinvariants hI :=
    { toFun x := ⟨x, x.2⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  have he : (coinvariantsCoalgHom hI).toLinearMap ∘ₗ e =
      (Subalgebra.toSubmodule I.coinvariants).subtype :=
    LinearMap.ext fun _ ↦ rfl
  refine ⟨e.lTensor _ z, ?_⟩
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, he, hz]

/-- The representation of `G ⧸ N` on the `N`-invariant vectors of `V`. -/
@[implicit_reducible]
private noncomputable def coinvariantsComodule (hI : I.IsNormal) :
    Comodule k (CommHopfAlgCat.coinvariants hI) (hI.weightSpaceOneSubcomodule V) :=
  Comodule.ofCorestrict (coinvariantsCoalgHom hI) (lTensor_coinvariantsCoalgHom_injective hI _)
    (lTensor_map_coinvariantsCoalgHom_injective hI _)
    (coact_mem_range_lTensor_coinvariantsCoalgHom V hI)

/-- An `N`-invariant vector is fixed by `G ⧸ N` exactly when it is fixed by `G`. -/
private theorem mem_fixedSubcomodule_coinvariantsComodule_iff (hI : I.IsNormal)
    {w : hI.weightSpaceOneSubcomodule V} :
    w ∈ (letI := coinvariantsComodule V hI; Comodule.fixedSubcomodule k
      (CommHopfAlgCat.coinvariants hI) _) ↔
      w ∈ Comodule.fixedSubcomodule k H (hI.weightSpaceOneSubcomodule V) :=
  Comodule.mem_fixedSubcomodule_ofCorestrict_iff _ _ _ _
    (map_one (CommHopfAlgCat.coinvariantsι hI).hom)

/-- A morphism of representations of `G` restricts to a morphism of the representations of
`G ⧸ N` on `N`-invariant vectors. -/
private noncomputable def coinvariantsComoduleHom (hI : I.IsNormal) {V' : Type w}
    [AddCommMonoid V'] [Module k V'] [Comodule k H V'] (f : Comodule.Hom k H V V') :
    letI := coinvariantsComodule V hI
    letI := coinvariantsComodule V' hI
    Comodule.Hom k (CommHopfAlgCat.coinvariants hI) (hI.weightSpaceOneSubcomodule V)
      (hI.weightSpaceOneSubcomodule V') :=
  Comodule.Hom.ofCorestrict _ _ _ _ _ _ _ <|
    (f.comp (Subcomodule.subtype _)).codRestrict _ fun w ↦ by
      have hcomm : TensorProduct.map LinearMap.id (Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap ∘ₗ
          TensorProduct.map f.toLinearMap LinearMap.id =
            TensorProduct.map f.toLinearMap LinearMap.id ∘ₗ
              TensorProduct.map LinearMap.id (Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap := by
        change (Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap.lTensor _ ∘ₗ
            TensorProduct.map f.toLinearMap LinearMap.id =
          TensorProduct.map f.toLinearMap LinearMap.id ∘ₗ
            (Ideal.Quotient.mkₐ k I.toIdeal).toLinearMap.lTensor _
        rw [LinearMap.lTensor_comp_map, LinearMap.map_comp_lTensor]
        simp
      rw [HopfIdeal.IsNormal.mem_weightSpaceOneSubcomodule, Comodule.Hom.comp_apply,
        Subcomodule.subtype_apply, ← Comodule.Hom.map_coact_apply, ← LinearMap.comp_apply, hcomm,
        LinearMap.comp_apply, hI.mem_weightSpaceOneSubcomodule.1 w.2, TensorProduct.map_tmul,
        LinearMap.id_apply, Comodule.Hom.coe_toLinearMap]

/-- The restricted morphism acts as the original one on underlying vectors. -/
private theorem coe_coinvariantsComoduleHom_apply (hI : I.IsNormal) {V' : Type w}
    [AddCommMonoid V'] [Module k V'] [Comodule k H V'] (f : Comodule.Hom k H V V')
    (w : hI.weightSpaceOneSubcomodule V) :
    (coinvariantsComoduleHom V hI f w : V') = f w := by
  rw [coinvariantsComoduleHom, Comodule.Hom.ofCorestrict_apply, Comodule.Hom.codRestrict_apply,
    Comodule.Hom.comp_apply, Subcomodule.subtype_apply]

/-- **An extension of linearly reductive groups is linearly reductive.** Let `N` be the normal
closed subgroup of `G` cut out by a normal Hopf ideal `I`. If `N` and the quotient `G ⧸ N`, whose
coordinate ring is the coinvariants of `I`, are linearly reductive, then so is `G`. -/
theorem linearlyReductiveCommHopfAlgProperty.of_quotient_of_coinvariants
    (hI : I.IsNormal)
    (hN : linearlyReductiveCommHopfAlgProperty k (CommHopfAlgCat.quotient H I))
    (hQ : linearlyReductiveCommHopfAlgProperty k (CommHopfAlgCat.coinvariants hI)) :
    linearlyReductiveCommHopfAlgProperty k H := by
  rw [linearlyReductiveCommHopfAlgProperty_iff] at hN hQ ⊢
  refine Coalgebra.isLinearlyReductive_iff_forall_fixedMap_surjective_of_surjective.2
    fun M N f hf n ↦ ?_
  -- Restricted to the subgroup, every `N`-invariant vector of the target lifts.
  let q := (Bialgebra.Quotient.mkBialgHom (R := k) I.toIdeal).toCoalgHom
  have hmem {V : Type u} [AddCommMonoid V] [Module k V] [Comodule k H V] {v : V} :
      v ∈ hI.weightSpaceOneSubcomodule V ↔
        v ∈ (letI : Comodule k (H ⧸ I.toIdeal) V := Comodule.Corestrict q;
          Comodule.fixedSubcomodule k (H ⧸ I.toIdeal) V) := by
    let _ : Comodule k (H ⧸ I.toIdeal) V := Comodule.Corestrict q
    rw [HopfIdeal.IsNormal.mem_weightSpaceOneSubcomodule, Comodule.mem_fixedSubcomodule,
      Comodule.corestrict_coact_apply]
    -- `q` is the quotient map `H → H ⧸ I`, bundled as a coalgebra morphism.
    rfl
  have hsurj : Function.Surjective (coinvariantsComoduleHom M hI f.hom) := by
    rintro ⟨y, hy⟩
    let _ : Comodule k (H ⧸ I.toIdeal) M := Comodule.Corestrict q
    let _ : Comodule k (H ⧸ I.toIdeal) N := Comodule.Corestrict q
    obtain ⟨⟨x, hx⟩, hxy⟩ :=
      (Comodule.corestrictHom q f.hom).fixedMap_surjective_of_isLinearlyReductive hN hf
        ⟨y, hmem.1 hy⟩
    refine ⟨⟨x, hmem.2 hx⟩, Subtype.ext ?_⟩
    rw [coe_coinvariantsComoduleHom_apply]
    simpa using congrArg Subtype.val hxy
  -- A `G`-invariant vector is `N`-invariant, and then fixed by `G ⧸ N`.
  have hnN : (n : N) ∈ hI.weightSpaceOneSubcomodule N := by
    rw [HopfIdeal.IsNormal.mem_weightSpaceOneSubcomodule, Comodule.mem_fixedSubcomodule.1 n.2,
      TensorProduct.map_tmul, LinearMap.id_apply, AlgHom.toLinearMap_apply, map_one]
  let n' : hI.weightSpaceOneSubcomodule N := ⟨n, hnN⟩
  have hn' : n' ∈ Comodule.fixedSubcomodule k H (hI.weightSpaceOneSubcomodule N) := by
    refine ((Subcomodule.subtype _).mem_fixedSubcomodule_iff_of_injective
      (fun a b h ↦ Subtype.ext (by simpa using h)) n').1 ?_
    simp [n']
  let _ := coinvariantsComodule M hI
  let _ := coinvariantsComodule N hI
  obtain ⟨⟨m, hm⟩, hmn⟩ :=
    (coinvariantsComoduleHom M hI f.hom).fixedMap_surjective_of_isLinearlyReductive hQ hsurj
      ⟨n', (mem_fixedSubcomodule_coinvariantsComodule_iff N hI).2 hn'⟩
  have hm' := (Subcomodule.subtype _).mem_fixedSubcomodule
    ((mem_fixedSubcomodule_coinvariantsComodule_iff M hI).1 hm)
  rw [Subcomodule.subtype_apply] at hm'
  refine ⟨⟨m, hm'⟩, Subtype.ext ?_⟩
  have hmn' := congrArg Subtype.val (congrArg Subtype.val hmn)
  rw [Comodule.Hom.fixedMap_apply, coe_coinvariantsComoduleHom_apply] at hmn'
  simpa using hmn'

/-- For a linearly reductive normal subgroup `N`, the group `G` is linearly reductive exactly when
the quotient `G ⧸ N` is. -/
theorem linearlyReductiveCommHopfAlgProperty_iff_coinvariants (hI : I.IsNormal)
    (hN : linearlyReductiveCommHopfAlgProperty k (CommHopfAlgCat.quotient H I)) :
    linearlyReductiveCommHopfAlgProperty k H ↔
      linearlyReductiveCommHopfAlgProperty k (CommHopfAlgCat.coinvariants hI) :=
  ⟨linearlyReductiveCommHopfAlgProperty.of_injective (CommHopfAlgCat.coinvariantsι hI)
      (CommHopfAlgCat.hopfSubalgebraι_injective hI.isHopfSubalgebra_coinvariants),
    linearlyReductiveCommHopfAlgProperty.of_quotient_of_coinvariants hI hN⟩

end

end TauCeti
