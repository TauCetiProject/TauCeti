/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Exact
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Center
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Conjugation

import TauCeti.Algebra.Exact.Basic

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
component-group API over an algebraically closed field `k` (with isogeny specializations in
`TauCeti.Algebra.AlgebraicGroup.Isogeny.Centralizer`):

* **Transport and trivial cases**:
  - `TauCeti.FiniteTypeCommHopfAlgCat.centralizerComponentGroupEquivOfEq`: transport across
    equalities of Lie algebra elements, with rational-point, `refl`, `symm`, and `trans` laws.
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
    particular when `toBialgHom f` and `dualCotangentMap (toBialgHom f)` are both injective
    (`centralizerComponentGroupMap_surjective_of_injective_of_injective_differential`).
  - Exactness at `A_K(x)` (`TauCeti.mulExact_centralizerComponentGroupMap_of_faithfullyFlat`,
    `TauCeti.mulExact_centralizerComponentGroupMap_of_le`, and their specializations):
    whenever `centralizerMap` is faithfully flat (in particular when `toBialgHom f` is faithfully
    flat with injective differential), the sequence `π₀(ker f ∩ C_K(x)) → A_K(x) → A_H(df(x))` is
    exact at `A_K(x)`; when moreover `centralizerHopfIdeal K x ≤ kernelHopfIdeal f.hom` (in
    particular when `ker f` is central), this specializes to `π₀(ker f) → A_K(x) → A_H(df(x))`
    and characterizes injectivity by `(ker f)(k) ⊆ C_K(x)°(k)`
    (`injective_centralizerComponentGroupMap_iff_of_le` and its central-kernel specialization).

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
      (centralizerHopfIdeal H y).ComponentGroup :=
  HopfIdeal.componentGroupEquivOfEq (congrArg (centralizerHopfIdeal (H := H.obj)) hxy)

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
  rw [centralizerComponentGroupEquivOfEq]
  exact HopfIdeal.componentGroupEquivOfEq_rationalComponentMap rfl g

/-- Reflexive transport on centralizer component groups is the identity equivalence. -/
@[simp]
theorem centralizerComponentGroupEquivOfEq_refl (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) (h : x = x) :
    centralizerComponentGroupEquivOfEq H h =
      MulEquiv.refl (centralizerHopfIdeal H x).ComponentGroup :=
  HopfIdeal.componentGroupEquivOfEq_refl _ _

/-- The inverse of a centralizer component-group transport is transport along the symmetric
equality. -/
@[simp]
theorem centralizerComponentGroupEquivOfEq_symm (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    {x y : Module.Dual k (Bialgebra.CotangentSpace k H)} (hxy : x = y) :
    (centralizerComponentGroupEquivOfEq H hxy).symm =
      centralizerComponentGroupEquivOfEq H hxy.symm :=
  HopfIdeal.componentGroupEquivOfEq_symm _

/-- Composing two centralizer component-group transports gives the transport along the transitive
equality. -/
@[simp]
theorem centralizerComponentGroupEquivOfEq_trans (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    {x y z : Module.Dual k (Bialgebra.CotangentSpace k H)} (hxy : x = y) (hyz : y = z) :
    (centralizerComponentGroupEquivOfEq H hxy).trans
        (centralizerComponentGroupEquivOfEq H hyz) =
      centralizerComponentGroupEquivOfEq H (hxy.trans hyz) :=
  HopfIdeal.componentGroupEquivOfEq_trans _ _

/-- The centralizer component group of `0` is canonically isomorphic to `π₀(G)`. -/
noncomputable def centralizerComponentGroupZeroEquiv (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    (centralizerHopfIdeal H (0 : Module.Dual k (Bialgebra.CotangentSpace k H))).ComponentGroup ≃*
      ConnectedComponents (PrimeSpectrum H) :=
  HopfIdeal.componentGroupEquivOfEqBot (centralizerHopfIdeal_zero (k := k) (H := H))

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
      rationalComponentMap H g.val :=
  HopfIdeal.componentGroupEquivOfEqBot_rationalComponentMap
    (centralizerHopfIdeal_zero (k := k) (H := H)) g

/-- If `G` is connected, the homomorphism `A(x) →* π₀(G)` induced by the centralizer inclusion
`C_G(x) ⊆ G` is trivial (even though `A(x)` itself may be nontrivial). -/
theorem componentGroupInclusion_centralizer_eq_one (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    [ConnectedSpace (PrimeSpectrum H)]
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (C : (centralizerHopfIdeal H x).ComponentGroup) :
    (centralizerHopfIdeal H x).componentGroupInclusion C = 1 :=
  HopfIdeal.componentGroupInclusion_eq_one (centralizerHopfIdeal H x) C

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
@[simp]
theorem centralizerComponentGroupConjugationEquiv_one
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    (centralizerComponentGroupConjugationEquiv x 1).trans
        (centralizerComponentGroupEquivOfEq H
          (by rw [map_one]; exact one_apply_eq_self x)) =
      MulEquiv.refl (centralizerHopfIdeal H x).ComponentGroup :=
  (HopfIdeal.componentGroupConjugationEquiv_trans_componentGroupEquivOfEq _ _ _ 1 _ _).trans
    (HopfIdeal.componentGroupConjugationEquiv_one _)

/-- Conjugating a centralizer component group by `g` and then by `g'` agrees with conjugating by
`g' * g`, modulo canonical transport along `Ad(g')(Ad(g) x) = Ad(g' * g) x`. -/
@[simp]
theorem centralizerComponentGroupConjugationEquiv_trans
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (g g' : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (centralizerComponentGroupConjugationEquiv x g).trans
        (centralizerComponentGroupConjugationEquiv
          (Comodule.basePointsRepresentation (H := H) _ g x) g') =
      (centralizerComponentGroupConjugationEquiv x (g' * g)).trans
        (centralizerComponentGroupEquivOfEq H
          (by rw [map_mul]; exact mul_apply_eq_comp _ _ x)) :=
  (HopfIdeal.componentGroupConjugationEquiv_trans _ _ _ g g' _ _).trans
    (HopfIdeal.componentGroupConjugationEquiv_trans_componentGroupEquivOfEq
      _ _ _ (g' * g) _ _).symm

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
      MulAut.conj ((centralizerHopfIdeal H x).rationalComponentMap g) :=
  (HopfIdeal.componentGroupConjugationEquiv_trans_componentGroupEquivOfEq
      (centralizerHopfIdeal H x) _ _ g.val _ _).trans
    (HopfIdeal.componentGroupConjugationEquiv_self_eq_conj (centralizerHopfIdeal H x) g)

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
@[simp]
theorem centralizerComponentGroupMap_id (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    (centralizerComponentGroupEquivOfEq H
          (x := dualCotangentMap (toBialgHom (𝟙 H)) x) (y := x)
          (by rw [toBialgHom_id, dualCotangentMap_id, LinearMap.id_apply]) : _ →* _).comp
        (centralizerComponentGroupMap (𝟙 H) x) =
      MonoidHom.id (centralizerHopfIdeal H x).ComponentGroup := by
  rw [← MulEquiv.toMonoidHom_eq_coe]
  exact (HopfIdeal.componentGroupEquivOfEq_comp_componentGroupMap _ (centralizerHopfIdeal H x)
    (𝟙 H) _).trans (HopfIdeal.componentGroupMap_id (centralizerHopfIdeal H x) _)

/-- `centralizerComponentGroupMap` is contravariantly functorial in coordinate homomorphisms,
modulo canonical transport along `df(dg(x)) = d(g ∘ f)(x)`. -/
@[simp]
theorem centralizerComponentGroupMap_comp {L : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (g : K ⟶ L) (x : Module.Dual k (Bialgebra.CotangentSpace k L)) :
    (centralizerComponentGroupEquivOfEq H
          (x := dualCotangentMap (toBialgHom f) (dualCotangentMap (toBialgHom g) x))
          (y := dualCotangentMap (toBialgHom (f ≫ g)) x)
          (by rw [toBialgHom_comp, dualCotangentMap_comp, LinearMap.comp_apply]) : _ →* _).comp
        ((centralizerComponentGroupMap f (dualCotangentMap (toBialgHom g) x)).comp
          (centralizerComponentGroupMap g x)) =
      centralizerComponentGroupMap (f ≫ g) x := by
  rw [← MulEquiv.toMonoidHom_eq_coe, ← MonoidHom.comp_assoc, centralizerComponentGroupMap,
    centralizerComponentGroupMap, centralizerComponentGroupEquivOfEq,
    HopfIdeal.componentGroupEquivOfEq_comp_componentGroupMap, HopfIdeal.componentGroupMap_comp,
    centralizerComponentGroupMap]

/-- `centralizerComponentGroupMap` equals the component-group map of the coordinate arrow
`BialgHom.centralizerMap`. -/
theorem centralizerComponentGroupMap_eq_mapComponentGroup (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    centralizerComponentGroupMap f x =
      mapComponentGroup (ofHom ((toBialgHom f).centralizerMap x)) := by
  rw [centralizerComponentGroupMap, HopfIdeal.componentGroupMap_eq_mapComponentGroup]
  congr 1
  apply mkQuotient_hom_ext
  rw [mkQuotient_comp_quotientMap]
  apply ObjectProperty.hom_ext
  change f.hom ≫ _root_.CommHopfAlgCat.mkQuotient K.obj _ =
    _root_.CommHopfAlgCat.mkQuotient H.obj _ ≫
      _root_.CommHopfAlgCat.ofHom ((toBialgHom f).centralizerMap x)
  rw [_root_.CommHopfAlgCat.ofHom_centralizerMap, _root_.CommHopfAlgCat.mkQuotient_comp_quotientMap]
  apply _root_.CommHopfAlgCat.hom_ext
  rfl

/-- `centralizerComponentGroupMap` commutes with the homomorphisms `A_K(x) →* π₀(K)` and
`A_H(df(x)) →* π₀(H)` induced by the centralizer inclusions into the ambient groups. -/
theorem componentGroupInclusion_centralizerComponentGroupMap (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (C : (centralizerHopfIdeal K x).ComponentGroup) :
    (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)).componentGroupInclusion
        (centralizerComponentGroupMap f x C) =
      mapComponentGroup f ((centralizerHopfIdeal K x).componentGroupInclusion C) :=
  DFunLike.congr_fun
    (HopfIdeal.componentGroupInclusion_comp_componentGroupMap _ _ f
      ((toBialgHom f).map_centralizerHopfIdeal_le x)) C

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
theorem centralizerComponentGroupMap_surjective_of_injective_of_injective_differential
    (f : H ⟶ K) (hf : Function.Injective (toBialgHom f))
    (hinj : Function.Injective (dualCotangentMap (toBialgHom f)))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Surjective (centralizerComponentGroupMap f x) :=
  centralizerComponentGroupMap_surjective f hf x
    ((toBialgHom f).map_centralizerHopfIdeal_eq_of_injective hinj x)

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

/-- For a faithfully flat homomorphism `f` with injective differential, the sequence
`π₀(ker f ∩ C_K(x)) → A_K(x) → A_H(df(x))` is exact at `A_K(x)`. -/
theorem mulExact_centralizerComponentGroupMap_of_faithfullyFlat_of_injective_differential
    (f : H ⟶ K) (hf : (toBialgHom f).toAlgHom.toRingHom.FaithfullyFlat)
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
    ((toBialgHom f).faithfullyFlat_centralizerMap_of_injective hf hinj x)

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
  dsimp only at hex
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
  have hsurj : Function.Surjective (mapComponentGroup iso.hom) := fun D ↦ by
    obtain ⟨E, rfl⟩ := (mapComponentGroupMulEquiv iso).surjective D
    exact ⟨E, (mapComponentGroupMulEquiv_apply iso E).symm⟩
  rw [← hcomp, mapComponentGroup_comp, MonoidHom.coe_comp] at hex
  exact (Function.MulExact.comp_iff_of_surjective hsurj).mp hex

/-- **Central-kernel exact sequence on centralizer component groups.** For a faithfully flat
homomorphism `f` with injective differential and central kernel, the natural sequence
`π₀(ker f) → A_K(x) → A_H(df(x))` is exact at `A_K(x)`. -/
theorem
    mulExact_centralizerComponentGroupMap_of_faithfullyFlat_of_injective_differential_of_isCentral
    (f : H ⟶ K) (hf : (toBialgHom f).toAlgHom.toRingHom.FaithfullyFlat)
    (hinj : Function.Injective (dualCotangentMap (toBialgHom f)))
    (hcent : (CommHopfAlgCat.kernelHopfIdeal f.hom).IsCentral)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K (centralizerHopfIdeal_le_of_isCentral hcent x)))
      (centralizerComponentGroupMap f x) :=
  mulExact_centralizerComponentGroupMap_of_le f x
    ((toBialgHom f).faithfullyFlat_centralizerMap_of_injective hf hinj x)
    (centralizerHopfIdeal_le_of_isCentral hcent x)

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
  rw [← MonoidHom.ker_eq_bot_iff, hex.monoidHom_ker_eq, MonoidHom.range_eq_map,
    ← MonoidHom.range_eq_top_of_surjective _
      (CommHopfAlgCat.kernelHopfIdeal f.hom).rationalComponentMap_surjective,
    ← MonoidHom.range_comp, MonoidHom.range_eq_map, Subgroup.map_eq_bot_iff, top_le_iff,
    Subgroup.eq_top_iff']
  refine ⟨fun h g hg ↦ ?_, fun h gK ↦ ?_⟩
  · have h1 := h ⟨g, hg⟩
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
      mapComponentGroup_quotientMapOfLe_rationalComponentMap,
      (centralizerHopfIdeal K x).rationalComponentMap_eq_one_iff] at h1
    exact h1
  · rw [MonoidHom.mem_ker, MonoidHom.comp_apply,
      mapComponentGroup_quotientMapOfLe_rationalComponentMap,
      (centralizerHopfIdeal K x).rationalComponentMap_eq_one_iff]
    exact h gK.property

/-- For a faithfully flat homomorphism with injective differential and central kernel,
`A_K(x) → A_H(df(x))` is injective if and only if every rational point of `ker f` lies in
`C_K(x)°(k)`. -/
theorem
injective_centralizerComponentGroupMap_iff_of_faithfullyFlat_of_injective_differential_of_isCentral
    (f : H ⟶ K) (hf : (toBialgHom f).toAlgHom.toRingHom.FaithfullyFlat)
    (hinj : Function.Injective (dualCotangentMap (toBialgHom f)))
    (hcent : (CommHopfAlgCat.kernelHopfIdeal f.hom).IsCentral)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Injective (centralizerComponentGroupMap f x) ↔
      CommHopfAlgCat.quotientPointsSubgroup K.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)
          (CommAlgCat.of k k) ≤
        CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x).identityComponent
          (CommAlgCat.of k k) :=
  injective_centralizerComponentGroupMap_iff_of_le f x
    ((toBialgHom f).faithfullyFlat_centralizerMap_of_injective hf hinj x)
    (centralizerHopfIdeal_le_of_isCentral hcent x)

end Map

end TauCeti
