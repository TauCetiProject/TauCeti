/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Action
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Exact
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Central
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Centralizer
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Center
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Conjugation

import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Conjugation

/-!
# Component groups of centralizers of Lie algebra elements

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k`, with
Lie algebra `𝔤`, and let `x ∈ 𝔤`. The component group of the centralizer is the finite group
`A(x) = π₀(C_G(x))`, written `(centralizerHopfIdeal H x).ComponentGroup`. By the general theory
of component groups of closed subgroups (`TauCeti.HopfIdeal.quotientMulEquivComponentGroup`) it is
`C_G(x)(k) ⧸ C_G(x)°(k)`, and `TauCeti.HopfIdeal.componentGroupInclusion` induces the
homomorphism `A(x) →* π₀(G)` from the inclusion `C_G(x) ⊆ G`. Actions and homomorphisms on
`C_G(x)(k)` trivial on `C_G(x)°(k)` descend to `A(x)` via the closed-subgroup API in
`TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Action`.

Scheme-theoretic containment of central subgroups (including `Z(G)`) and the kernel of
`BialgHom.centralizerMap` are developed over an arbitrary field in
`TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Map` and
`TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Center`. This file develops the
component-group API over an algebraically closed field `k`:

* **Transport and trivial cases**:
  - `TauCeti.FiniteTypeCommHopfAlgCat.centralizerComponentGroupEquivOfEq`: transport across
    equalities of Lie algebra elements.
  - `TauCeti.FiniteTypeCommHopfAlgCat.centralizerComponentGroupZeroEquiv`: `A(0) ≃* π₀(G)`.
  - `TauCeti.FiniteTypeCommHopfAlgCat.componentGroupInclusion_centralizer_eq_one`: the
    homomorphism `A(x) →* π₀(G)` induced by `C_G(x) ⊆ G` is trivial when `G` is connected.
* **Conjugation**:
  - `TauCeti.centralizerComponentGroupConjugationEquiv`: a rational point `g ∈ G(k)` induces
    `A(x) ≃* A(Ad(g) x)`, satisfying identity (`centralizerComponentGroupConjugationEquiv_one`),
    composition (`centralizerComponentGroupConjugationEquiv_trans`), and inner self-conjugation
    for `g ∈ C_G(x)(k)` (`centralizerComponentGroupConjugationEquiv_self_eq_conj`).
* **Homomorphisms and exact sequences**:
  - `TauCeti.centralizerComponentGroupMap`: a homomorphism `φ : G' → G` (with coordinate arrow
    `f : H ⟶ K`) induces `A_G'(x) →* A_G(dφ x)`, functorial in `f`
    (`centralizerComponentGroupMap_id`, `centralizerComponentGroupMap_comp`), natural under
    conjugation (`centralizerComponentGroupMap_conjugationEquiv`), compatible with the
    homomorphisms `A_K(x) →* π₀(K)` and `A_H(df(x)) →* π₀(H)` induced by the centralizer
    inclusions (`componentGroupInclusion_centralizerComponentGroupMap`), and equal to
    `mapComponentGroup (ofHom ((toBialgHom f).centralizerMap x))`
    (`centralizerComponentGroupMap_eq_mapComponentGroup`).
  - Surjectivity (`TauCeti.centralizerComponentGroupMap_surjective`): holds when `toBialgHom f`
    is injective and `C_G'(x)` is the scheme-theoretic inverse image of `C_G(dφ x)`, in
    particular when `dualCotangentMap (toBialgHom f)` is injective
    (`centralizerComponentGroupMap_surjective_of_injective_differential`), for isogenies of
    smooth groups with étale kernel (`centralizerComponentGroupMap_surjective_of_etaleKernel`),
    and for characteristic-zero isogenies (`centralizerComponentGroupMap_surjective_of_isIsogeny`).
  - Exactness at `A_K(x)` (`TauCeti.mulExact_centralizerComponentGroupMap_of_faithfullyFlat`,
    `mulExact_centralizerComponentGroupMap_of_le`): whenever `centralizerMap` is faithfully flat,
    the sequence `π₀(ker f ∩ C_K(x)) → A_K(x) → A_H(df(x))` is exact at `A_K(x)` (with
    surjectivity at `A_H(df(x))` given separately by `centralizerComponentGroupMap_surjective`
    and its corollaries); when moreover `centralizerHopfIdeal K x ≤ kernelHopfIdeal f.hom` (in
    particular when `ker f` is central), this specializes to `π₀(ker f) → A_K(x) → A_H(df(x))`
    and characterizes injectivity by `(ker f)(k) ⊆ C_K(x)°(k)`
    (`injective_centralizerComponentGroupMap_iff_of_le`,
    `injective_centralizerComponentGroupMap_iff_of_isCentral`).

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.1, for the component groups `A(x)` of centralizers.
* J. C. Jantzen, *Nilpotent Orbits in Representation Theory*, Progress in Mathematics 228,
  Birkhäuser, 2004, §3.
* J. S. Milne, *Algebraic Groups* (2017), Proposition 2.37 and Chapters 5, 10, and 18.
-/

public section

open CategoryTheory Derivation WithConv

namespace TauCeti

universe u

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k] [IsAlgClosed k]

/-- Transport a centralizer component group across an equality of Lie algebra elements. -/
noncomputable def centralizerComponentGroupEquivOfEq (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    {x y : Module.Dual k (Bialgebra.CotangentSpace k H)} (hxy : x = y) :
    (centralizerHopfIdeal H x).ComponentGroup ≃*
      (centralizerHopfIdeal H y).ComponentGroup := by
  subst hxy
  exact MulEquiv.refl _

/-- Transporting a rational-point component class along an equality of Lie algebra elements
preserves the underlying rational point. -/
@[simp]
theorem centralizerComponentGroupEquivOfEq_rationalComponentMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    {x y : Module.Dual k (Bialgebra.CotangentSpace k H)} (hxy : x = y)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) :
    centralizerComponentGroupEquivOfEq H hxy ((centralizerHopfIdeal H x).rationalComponentMap g) =
      (centralizerHopfIdeal H y).rationalComponentMap ⟨g.val, hxy ▸ g.property⟩ := by
  subst hxy
  rfl

/-- The centralizer component group of `0` is canonically isomorphic to `π₀(G)`. -/
noncomputable def centralizerComponentGroupZeroEquiv (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (centralizerHopfIdeal H (0 : Module.Dual k (Bialgebra.CotangentSpace k H))).ComponentGroup ≃*
      ConnectedComponents (PrimeSpectrum H) :=
  let e : H ≅ quotient H (centralizerHopfIdeal H 0) :=
    (quotientBotIso H).symm ≪≫
      eqToIso (congrArg (quotient H) (centralizerHopfIdeal_zero (k := k) (H := H)).symm)
  mapComponentGroupMulEquiv e

/-- On rational points, the canonical isomorphism `A(0) ≃* π₀(G)` sends the component of a
centralizer point `g ∈ C_G(0)(k)` to its ambient component in `π₀(G)`. -/
@[simp]
theorem centralizerComponentGroupZeroEquiv_rationalComponentMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj
      (centralizerHopfIdeal H (0 : Module.Dual k (Bialgebra.CotangentSpace k H)))
      (CommAlgCat.of k k)) :
    centralizerComponentGroupZeroEquiv H
        ((centralizerHopfIdeal H 0).rationalComponentMap g) =
      rationalComponentMap H g.val := by
  have he :
      ((quotientBotIso H).symm ≪≫
        eqToIso (congrArg (quotient H) (centralizerHopfIdeal_zero (k := k) (H := H)).symm)).hom =
        mkQuotient H (centralizerHopfIdeal H 0) := by
    rw [Iso.trans_hom, Iso.symm_hom, quotientBotIso_inv, eqToIso.hom,
      mkQuotient_comp_eqToHom (centralizerHopfIdeal_zero (k := k) (H := H))]
  rw [centralizerComponentGroupZeroEquiv, mapComponentGroupMulEquiv_apply, he]
  exact (centralizerHopfIdeal H 0).componentGroupInclusion_rationalComponentMap g

/-- If `G` is connected, the homomorphism `A(x) →* π₀(G)` induced by the centralizer inclusion
`C_G(x) ⊆ G` is trivial (even though `A(x)` itself may be nontrivial). -/
theorem componentGroupInclusion_centralizer_eq_one (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    [ConnectedSpace (PrimeSpectrum H)]
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (C : (centralizerHopfIdeal H x).ComponentGroup) :
    (centralizerHopfIdeal H x).componentGroupInclusion C = 1 :=
  Subsingleton.elim _ _

end FiniteTypeCommHopfAlgCat

open FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k] [IsAlgClosed k]

attribute [local instance] Derivation.adjointComodule

section Conjugation

variable {H : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **Conjugation of centralizer component groups.** Conjugation by a rational point `g` of `G`
identifies the component group of `C_G(x)` with that of `C_G(Ad(g) x) = g C_G(x) g⁻¹`. -/
noncomputable def centralizerComponentGroupConjugationEquiv
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (centralizerHopfIdeal H x).ComponentGroup ≃*
      (centralizerHopfIdeal H (Comodule.basePointsRepresentation (H := H) _ g x)).ComponentGroup :=
  HopfIdeal.componentGroupConjugationEquiv _ _ g
    (centralizerHopfIdeal_basePointsRepresentation x g)

/-- On rational points, conjugation of centralizer component groups sends the component of `c`
to the component of `gcg⁻¹`. -/
@[simp]
theorem centralizerComponentGroupConjugationEquiv_rationalComponentMap
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (c : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) :
    centralizerComponentGroupConjugationEquiv x g
        ((centralizerHopfIdeal H x).rationalComponentMap c) =
      HopfIdeal.rationalComponentMap
        (centralizerHopfIdeal H (Comodule.basePointsRepresentation (H := H) _ g x))
        ⟨g * c * g⁻¹, centralizerHopfIdeal_basePointsRepresentation x g ▸
          (CommHopfAlgCat.mul_mul_inv_mem_conjugate_iff _ g c).mpr c.property⟩ :=
  HopfIdeal.componentGroupConjugationEquiv_rationalComponentMap _ _ g _ c

/-- Conjugation by the identity point induces the identity of `A(x)`. -/
theorem centralizerComponentGroupConjugationEquiv_one
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    (centralizerComponentGroupConjugationEquiv x 1).trans
        (centralizerComponentGroupEquivOfEq H
          (by rw [map_one]; exact one_apply_eq_self x)) =
      MulEquiv.refl (centralizerHopfIdeal H x).ComponentGroup := by
  ext C
  obtain ⟨c, rfl⟩ := (centralizerHopfIdeal H x).rationalComponentMap_surjective C
  rw [MulEquiv.trans_apply, centralizerComponentGroupConjugationEquiv_rationalComponentMap,
    centralizerComponentGroupEquivOfEq_rationalComponentMap, MulEquiv.refl_apply]
  refine congrArg (centralizerHopfIdeal H x).rationalComponentMap (Subtype.ext ?_)
  simp only [one_mul, inv_one, mul_one]

/-- Conjugating a centralizer component group by `g` and then by `g'` agrees with conjugating by
`g' * g`, modulo canonical transport along `Ad(g')(Ad(g) x) = Ad(g' * g) x`. -/
theorem centralizerComponentGroupConjugationEquiv_trans
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (g g' : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (centralizerComponentGroupConjugationEquiv x g).trans
        (centralizerComponentGroupConjugationEquiv
          (Comodule.basePointsRepresentation (H := H) _ g x) g') =
      (centralizerComponentGroupConjugationEquiv x (g' * g)).trans
        (centralizerComponentGroupEquivOfEq H
          (by rw [map_mul]; exact mul_apply_eq_comp _ _ x)) := by
  ext C
  obtain ⟨c, rfl⟩ := (centralizerHopfIdeal H x).rationalComponentMap_surjective C
  rw [MulEquiv.trans_apply, MulEquiv.trans_apply,
    centralizerComponentGroupConjugationEquiv_rationalComponentMap,
    centralizerComponentGroupConjugationEquiv_rationalComponentMap,
    centralizerComponentGroupConjugationEquiv_rationalComponentMap,
    centralizerComponentGroupEquivOfEq_rationalComponentMap]
  refine congrArg _ (Subtype.ext ?_)
  simp only [mul_assoc, mul_inv_rev]

/-- Self-conjugation by a rational point `g ∈ C_G(x)(k)` acts on `A(x)` by inner conjugation by
`[g] ∈ A(x)`. -/
theorem centralizerComponentGroupConjugationEquiv_self_eq_conj
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) :
    (centralizerComponentGroupConjugationEquiv x g.val).trans
        (centralizerComponentGroupEquivOfEq H
          ((Comodule.mem_quotientPointsSubgroup_stabilizerHopfIdeal_iff x g.val).mp
            ((CommHopfAlgCat.mem_quotientPointsSubgroup_iff _ _ _ _).mpr
              (by simpa only [centralizerHopfIdeal_def] using
                (CommHopfAlgCat.mem_quotientPointsSubgroup_iff H.obj _ _ _).mp g.property)))) =
      MulAut.conj ((centralizerHopfIdeal H x).rationalComponentMap g) := by
  rw [← HopfIdeal.componentGroupConjugationEquiv_self_eq_conj (centralizerHopfIdeal H x) g]
  ext C
  obtain ⟨c, rfl⟩ := (centralizerHopfIdeal H x).rationalComponentMap_surjective C
  rw [MulEquiv.trans_apply, centralizerComponentGroupConjugationEquiv_rationalComponentMap,
    centralizerComponentGroupEquivOfEq_rationalComponentMap,
    HopfIdeal.componentGroupConjugationEquiv_rationalComponentMap]

end Conjugation

section Map

variable {H K : FiniteTypeCommHopfAlgCat.{u, u} k}

/-- **Centralizer component groups under homomorphisms.** A homomorphism `φ : G' → G` of affine
groups induces `π₀(C_G'(x)) →* π₀(C_G(dφ x))`. -/
noncomputable def centralizerComponentGroupMap (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    (centralizerHopfIdeal K x).ComponentGroup →*
      (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)).ComponentGroup :=
  HopfIdeal.componentGroupMap _ _ f ((toBialgHom f).map_centralizerHopfIdeal_le x)

/-- On rational points, the induced map of centralizer component groups sends the component of
`c` to the component of `φ(c)`. -/
@[simp]
theorem centralizerComponentGroupMap_rationalComponentMap (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (c : CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x)
      (CommAlgCat.of k k)) :
    centralizerComponentGroupMap f x ((centralizerHopfIdeal K x).rationalComponentMap c) =
      (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)).rationalComponentMap
        ⟨BialgHom.mapDomain (A := k) (toBialgHom f) c,
          CommHopfAlgCat.mapDomain_mem_quotientPointsSubgroup_of_map_le f.hom
            ((toBialgHom f).map_centralizerHopfIdeal_le x) _ c.property⟩ :=
  HopfIdeal.componentGroupMap_rationalComponentMap _ _ f _ c

/-- Along the identity morphism, `centralizerComponentGroupMap` is the identity modulo canonical
transport along `d(id)(x) = x`. -/
theorem centralizerComponentGroupMap_id (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    (centralizerComponentGroupEquivOfEq H
        (by rw [toBialgHom_id, dualCotangentMap_id, LinearMap.id_apply])).toMonoidHom.comp
        (centralizerComponentGroupMap (𝟙 H) x) =
      MonoidHom.id (centralizerHopfIdeal H x).ComponentGroup := by
  ext C
  obtain ⟨c, rfl⟩ := (centralizerHopfIdeal H x).rationalComponentMap_surjective C
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    centralizerComponentGroupMap_rationalComponentMap,
    centralizerComponentGroupEquivOfEq_rationalComponentMap, MonoidHom.id_apply]
  refine congrArg (centralizerHopfIdeal H x).rationalComponentMap (Subtype.ext ?_)
  simp only [toBialgHom_id, BialgHom.mapDomain_id, MonoidHom.id_apply]

/-- `centralizerComponentGroupMap` is contravariantly functorial in coordinate homomorphisms,
modulo canonical transport along `df(dg(x)) = d(g ∘ f)(x)`. -/
theorem centralizerComponentGroupMap_comp {L : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (g : K ⟶ L) (x : Module.Dual k (Bialgebra.CotangentSpace k L)) :
    (centralizerComponentGroupEquivOfEq H
        (by rw [toBialgHom_comp, dualCotangentMap_comp, LinearMap.comp_apply])).toMonoidHom.comp
        ((centralizerComponentGroupMap f (dualCotangentMap (toBialgHom g) x)).comp
          (centralizerComponentGroupMap g x)) =
      centralizerComponentGroupMap (f ≫ g) x := by
  ext C
  obtain ⟨c, rfl⟩ := (centralizerHopfIdeal L x).rationalComponentMap_surjective C
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    centralizerComponentGroupMap_rationalComponentMap,
    centralizerComponentGroupMap_rationalComponentMap,
    centralizerComponentGroupEquivOfEq_rationalComponentMap,
    centralizerComponentGroupMap_rationalComponentMap]
  refine congrArg _ (Subtype.ext ?_)
  simp only [toBialgHom_comp, BialgHom.mapDomain_comp, MonoidHom.comp_apply]

/-- `centralizerComponentGroupMap` equals the component-group map of the coordinate arrow
`BialgHom.centralizerMap`. -/
theorem centralizerComponentGroupMap_eq_mapComponentGroup (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    centralizerComponentGroupMap f x =
      mapComponentGroup (ofHom ((toBialgHom f).centralizerMap x)) := by
  unfold centralizerComponentGroupMap HopfIdeal.componentGroupMap
  congr 1
  apply ObjectProperty.hom_ext
  apply _root_.CommHopfAlgCat.hom_ext
  ext a
  obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective a
  exact (quotientMap_mk _ _ f _ y).trans ((toBialgHom f).centralizerMap_mk x y).symm

/-- `centralizerComponentGroupMap` commutes with the homomorphisms `A_K(x) →* π₀(K)` and
`A_H(df(x)) →* π₀(H)` induced by the centralizer inclusions into the ambient groups. -/
theorem componentGroupInclusion_centralizerComponentGroupMap (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (C : (centralizerHopfIdeal K x).ComponentGroup) :
    (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)).componentGroupInclusion
        (centralizerComponentGroupMap f x C) =
      mapComponentGroup f ((centralizerHopfIdeal K x).componentGroupInclusion C) := by
  obtain ⟨g, rfl⟩ := (centralizerHopfIdeal K x).rationalComponentMap_surjective C
  rw [centralizerComponentGroupMap_rationalComponentMap,
    HopfIdeal.componentGroupInclusion_rationalComponentMap,
    HopfIdeal.componentGroupInclusion_rationalComponentMap,
    mapComponentGroup_rationalComponentMap]

/-- `centralizerComponentGroupMap` commutes with conjugation by a rational point `g ∈ K(k)`. -/
theorem centralizerComponentGroupMap_conjugationEquiv (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (g : HopfAlgebra.points (R := k) (H := K) (CommAlgCat.of k k))
    (C : (centralizerHopfIdeal K x).ComponentGroup) :
    centralizerComponentGroupEquivOfEq H
        ((toBialgHom f).dualCotangentMap_basePointsRepresentation g x)
        (centralizerComponentGroupMap f (Comodule.basePointsRepresentation (H := K) _ g x)
          (centralizerComponentGroupConjugationEquiv x g C)) =
      centralizerComponentGroupConjugationEquiv (dualCotangentMap (toBialgHom f) x)
        (BialgHom.mapDomain (A := k) (toBialgHom f) g)
        (centralizerComponentGroupMap f x C) := by
  obtain ⟨h, rfl⟩ := (centralizerHopfIdeal K x).rationalComponentMap_surjective C
  rw [centralizerComponentGroupConjugationEquiv_rationalComponentMap,
    centralizerComponentGroupMap_rationalComponentMap,
    centralizerComponentGroupEquivOfEq_rationalComponentMap,
    centralizerComponentGroupMap_rationalComponentMap,
    centralizerComponentGroupConjugationEquiv_rationalComponentMap]
  refine congrArg _ (Subtype.ext ?_)
  simp only [map_mul, map_inv]

/-- **Surjectivity of centralizer component group maps.** Let `φ : G' → G` be a homomorphism of
affine groups whose coordinate map is injective, so that `φ` is surjective on rational points,
and suppose `C_G'(x)` is the scheme-theoretic inverse image of `C_G(dφ x)`. Then
`π₀(C_G'(x)) →* π₀(C_G(dφ x))` is surjective. -/
theorem centralizerComponentGroupMap_surjective (f : H ⟶ K)
    (hf : Function.Injective (toBialgHom f))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (hx : (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)).map (toBialgHom f) =
      centralizerHopfIdeal K x) :
    Function.Surjective (centralizerComponentGroupMap f x) :=
  HopfIdeal.componentGroupMap_surjective _ _ f hf hx

/-- A homomorphism with injective coordinate map and injective differential induces a surjection
`A_K(x) ↠ A_H(df(x))`. -/
theorem centralizerComponentGroupMap_surjective_of_injective_differential (f : H ⟶ K)
    (hf : Function.Injective (toBialgHom f))
    (hinj : Function.Injective (dualCotangentMap (toBialgHom f)))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Surjective (centralizerComponentGroupMap f x) :=
  centralizerComponentGroupMap_surjective f hf x
    ((toBialgHom f).map_centralizerHopfIdeal_eq_of_injective hinj x)

/-- An isogeny of smooth affine groups with étale kernel induces a surjection
`A_K(x) ↠ A_H(df(x))`. -/
theorem centralizerComponentGroupMap_surjective_of_etaleKernel (f : H ⟶ K)
    (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hker : Algebra.Etale k (K ⧸ (CommHopfAlgCat.kernelHopfIdeal f.hom).toIdeal))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Surjective (centralizerComponentGroupMap f x) :=
  centralizerComponentGroupMap_surjective_of_injective_differential f hf.injective
    (hf.dualCotangentMap_bijective_of_etaleKernel hker).injective x

/-- In characteristic zero, an isogeny `φ : G' → G` induces a surjection
`π₀(C_G'(x)) →* π₀(C_G(dφ x))` of centralizer component groups. This includes central isogenies
of semisimple groups, for which the map need not be injective. -/
theorem centralizerComponentGroupMap_surjective_of_isIsogeny [CharZero k] (f : H ⟶ K)
    (hf : CommHopfAlgCat.IsIsogeny f.hom) (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Surjective (centralizerComponentGroupMap f x) :=
  centralizerComponentGroupMap_surjective f hf.injective x
    (hf.map_centralizerHopfIdeal_of_charZero x)

/-- Whenever the restricted coordinate map `BialgHom.centralizerMap` is faithfully flat, the
sequence `π₀(ker f ∩ C_K(x)) → A_K(x) → A_H(df(x))` is exact at `A_K(x)`. -/
theorem mulExact_centralizerComponentGroupMap_of_faithfullyFlat (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (hf : ((toBialgHom f).centralizerMap x).toAlgHom.toRingHom.FaithfullyFlat) :
    let c : quotient H (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)) ⟶
        quotient K (centralizerHopfIdeal K x) :=
      ofHom ((toBialgHom f).centralizerMap x)
    Function.MulExact
      (mapComponentGroup (mkQuotient (quotient K (centralizerHopfIdeal K x))
        (CommHopfAlgCat.kernelHopfIdeal c.hom)))
      (centralizerComponentGroupMap f x) := by
  intro c
  rw [centralizerComponentGroupMap_eq_mapComponentGroup]
  exact mulExact_mapComponentGroup_kernel c hf

/-- For an isogeny `f` with injective differential, the sequence
`π₀(ker f ∩ C_K(x)) → A_K(x) → A_H(df(x))` is exact at `A_K(x)` (and surjective at `A_H(df(x))`
by `centralizerComponentGroupMap_surjective_of_injective_differential`). -/
theorem mulExact_centralizerComponentGroupMap_of_injective_differential (f : H ⟶ K)
    (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hinj : Function.Injective (dualCotangentMap (toBialgHom f)))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    let c : quotient H (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)) ⟶
        quotient K (centralizerHopfIdeal K x) :=
      ofHom ((toBialgHom f).centralizerMap x)
    Function.MulExact
      (mapComponentGroup (mkQuotient (quotient K (centralizerHopfIdeal K x))
        (CommHopfAlgCat.kernelHopfIdeal c.hom)))
      (centralizerComponentGroupMap f x) :=
  mulExact_centralizerComponentGroupMap_of_faithfullyFlat f x
    (hf.centralizerMap_of_injective hinj x).faithfullyFlat

/-- Whenever `BialgHom.centralizerMap` is faithfully flat and `ker(f) ⊆ C_K(x)`, the sequence
`π₀(ker f) → A_K(x) → A_H(df(x))` is exact at `A_K(x)`. -/
theorem mulExact_centralizerComponentGroupMap_of_le (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (hf : ((toBialgHom f).centralizerMap x).toAlgHom.toRingHom.FaithfullyFlat)
    (hle : centralizerHopfIdeal K x ≤ CommHopfAlgCat.kernelHopfIdeal f.hom) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K hle))
      (centralizerComponentGroupMap f x) := by
  let c : quotient H (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)) ⟶
      quotient K (centralizerHopfIdeal K x) :=
    ofHom ((toBialgHom f).centralizerMap x)
  have hex := mulExact_centralizerComponentGroupMap_of_faithfullyFlat f x hf
  let _ := instGroupConnectedComponents
    (quotient (quotient K (centralizerHopfIdeal K x)) (CommHopfAlgCat.kernelHopfIdeal c.hom))
  let iso : quotient K (CommHopfAlgCat.kernelHopfIdeal f.hom) ≅
      quotient (quotient K (centralizerHopfIdeal K x)) (CommHopfAlgCat.kernelHopfIdeal c.hom) :=
    ObjectProperty.isoMk _ (f.hom.kernelCentralizerMapIso x hle)
  have hcomp :
      quotientMapOfLe K hle ≫ iso.hom =
        mkQuotient (quotient K (centralizerHopfIdeal K x))
          (CommHopfAlgCat.kernelHopfIdeal c.hom) :=
    ObjectProperty.hom_ext _
      (f.hom.quotientMapOfLe_comp_kernelCentralizerMapIso_hom x hle)
  have hrange :
      Set.range (mapComponentGroup (mkQuotient (quotient K (centralizerHopfIdeal K x))
          (CommHopfAlgCat.kernelHopfIdeal c.hom))) =
        Set.range (mapComponentGroup (quotientMapOfLe K hle)) := by
    have hmap :
        mapComponentGroup (mkQuotient (quotient K (centralizerHopfIdeal K x))
            (CommHopfAlgCat.kernelHopfIdeal c.hom)) =
          (mapComponentGroup (quotientMapOfLe K hle)).comp
            (mapComponentGroupMulEquiv iso).toMonoidHom := by
      have hiso : (mapComponentGroupMulEquiv iso).toMonoidHom = mapComponentGroup iso.hom :=
        MonoidHom.ext fun D ↦ mapComponentGroupMulEquiv_apply iso D
      rw [← hcomp, mapComponentGroup_comp, hiso]
    rw [hmap, MonoidHom.coe_comp]
    exact (mapComponentGroupMulEquiv iso).surjective.range_comp _
  intro C
  rw [hex C, hrange]

/-- **Central-isogeny exact sequence on centralizer component groups.** For an isogeny `f` with
injective differential and central kernel, the natural sequence
`π₀(ker f) → A_K(x) → A_H(df(x))` is exact at `A_K(x)` (and surjective at `A_H(df(x))` by
`centralizerComponentGroupMap_surjective_of_injective_differential`). -/
theorem mulExact_centralizerComponentGroupMap_of_isCentral (f : H ⟶ K)
    (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hinj : Function.Injective (dualCotangentMap (toBialgHom f)))
    (hcent : (CommHopfAlgCat.kernelHopfIdeal f.hom).IsCentral)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K (centralizerHopfIdeal_le_of_isCentral hcent x)))
      (centralizerComponentGroupMap f x) :=
  mulExact_centralizerComponentGroupMap_of_le f x
    (hf.centralizerMap_of_injective hinj x).faithfullyFlat
    (centralizerHopfIdeal_le_of_isCentral hcent x)

/-- Characteristic-zero central-isogeny exactness at `A_K(x)` in
`π₀(ker f) → A_K(x) → A_H(df(x))` (with surjectivity at `A_H(df(x))` given separately by
`centralizerComponentGroupMap_surjective_of_isIsogeny`). -/
theorem mulExact_centralizerComponentGroupMap_of_isCentralIsogeny_of_charZero [CharZero k]
    (f : H ⟶ K) (hf : CommHopfAlgCat.IsCentralIsogeny f.hom)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K
        (centralizerHopfIdeal_le_of_isCentral hf.isCentral_kernelHopfIdeal x)))
      (centralizerComponentGroupMap f x) :=
  mulExact_centralizerComponentGroupMap_of_isCentral f hf.isIsogeny
    hf.isIsogeny.dualCotangentMap_bijective_of_charZero.injective
    hf.isCentral_kernelHopfIdeal x

/-- In characteristic zero, every isogeny from a geometrically connected affine group is central
and therefore gives exactness at `A_K(x)` in `π₀(ker f) → A_K(x) → A_H(df(x))` (with
surjectivity at `A_H(df(x))` given separately by
`centralizerComponentGroupMap_surjective_of_isIsogeny`). -/
theorem mulExact_centralizerComponentGroupMap_of_isIsogeny_of_connected_of_charZero [CharZero k]
    (f : H ⟶ K) (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hK : geometricallyConnectedCommHopfAlgProperty k K.obj)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K
        (centralizerHopfIdeal_le_of_isCentral
          (hf.isCentralIsogeny_of_charZero hK).isCentral_kernelHopfIdeal x)))
      (centralizerComponentGroupMap f x) :=
  mulExact_centralizerComponentGroupMap_of_isCentralIsogeny_of_charZero f
    (hf.isCentralIsogeny_of_charZero hK) x

/-- Whenever `BialgHom.centralizerMap` is faithfully flat and `ker(f) ⊆ C_K(x)`,
`A_K(x) → A_H(df(x))` is injective if and only if every rational point of `ker f` lies in
`C_K(x)°(k)`. -/
theorem injective_centralizerComponentGroupMap_iff_of_le (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (hf : ((toBialgHom f).centralizerMap x).toAlgHom.toRingHom.FaithfullyFlat)
    (hle : centralizerHopfIdeal K x ≤ CommHopfAlgCat.kernelHopfIdeal f.hom) :
    Function.Injective (centralizerComponentGroupMap f x) ↔
      CommHopfAlgCat.quotientPointsSubgroup K.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)
          (CommAlgCat.of k k) ≤
        CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x).identityComponent
          (CommAlgCat.of k k) := by
  have hex := mulExact_centralizerComponentGroupMap_of_le f x hf hle
  rw [injective_iff_map_eq_one]
  constructor
  · intro hinjC g hg
    let gK : CommHopfAlgCat.quotientPointsSubgroup K.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)
        (CommAlgCat.of k k) := ⟨g, hg⟩
    let gC : CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x)
        (CommAlgCat.of k k) :=
      ⟨g, CommHopfAlgCat.quotientPointsSubgroup_le_of_le K.obj hle _ hg⟩
    have hmap : centralizerComponentGroupMap f x
        ((centralizerHopfIdeal K x).rationalComponentMap gC) = 1 := by
      rw [← mapComponentGroup_quotientMapOfLe_rationalComponentMap K hle gK]
      exact (hex _).mpr ⟨(CommHopfAlgCat.kernelHopfIdeal f.hom).rationalComponentMap gK, rfl⟩
    exact ((centralizerHopfIdeal K x).rationalComponentMap_eq_one_iff gC).mp (hinjC _ hmap)
  · intro hle' C hC
    obtain ⟨D, rfl⟩ := (hex C).mp hC
    obtain ⟨gK, rfl⟩ := (CommHopfAlgCat.kernelHopfIdeal f.hom).rationalComponentMap_surjective D
    rw [mapComponentGroup_quotientMapOfLe_rationalComponentMap]
    exact ((centralizerHopfIdeal K x).rationalComponentMap_eq_one_iff _).mpr (hle' gK.property)

/-- For a central isogeny with injective differential, `A_K(x) → A_H(df(x))` is injective (hence
an isomorphism, combined with `centralizerComponentGroupMap_surjective_of_injective_differential`)
if and only if every rational point of `ker f` lies in `C_K(x)°(k)`. -/
theorem injective_centralizerComponentGroupMap_iff_of_isCentral (f : H ⟶ K)
    (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hinj : Function.Injective (dualCotangentMap (toBialgHom f)))
    (hcent : (CommHopfAlgCat.kernelHopfIdeal f.hom).IsCentral)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Injective (centralizerComponentGroupMap f x) ↔
      CommHopfAlgCat.quotientPointsSubgroup K.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)
          (CommAlgCat.of k k) ≤
        CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x).identityComponent
          (CommAlgCat.of k k) :=
  injective_centralizerComponentGroupMap_iff_of_le f x
    (hf.centralizerMap_of_injective hinj x).faithfullyFlat
    (centralizerHopfIdeal_le_of_isCentral hcent x)

end Map

end TauCeti
