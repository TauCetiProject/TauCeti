/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Exact
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.ComponentGroup.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Center
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Map

public import TauCeti.Algebra.AlgebraicGroup.FiniteType.Tangent
import TauCeti.Algebra.Group.Subgroup.Ker

/-!
# Component groups of centralizers of Lie algebra elements

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k`, with
Lie algebra `𝔤`, and let `x ∈ 𝔤`. The component group of the centralizer is the finite group
`A(x) = π₀(C_G(x))`, written `(centralizerHopfIdeal H x).ComponentGroup`. By the general theory
of component groups of closed subgroups (`TauCeti.HopfIdeal.quotientMulEquivComponentGroup`) it is
`C_G(x)(k) ⧸ C_G(x)°(k)`, and `TauCeti.HopfIdeal.componentGroupInclusion` induces the
homomorphism `A(x) →* π₀(G)` from the inclusion `C_G(x) ⊆ G`. Actions and homomorphisms on
`C_G(x)(k)` trivial on `C_G(x)°(k)` descend to `A(x)` via the closed-subgroup API in
`TauCeti.Algebra.AlgebraicGroup.HopfIdeal.ComponentGroup.Action`.

Scheme-theoretic containment of central subgroups (including `Z(G)`) and the kernel of
`BialgHom.centralizerMap` are developed over an arbitrary field in
`TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Map` and
`TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Center`. This file develops the
component-group API over an algebraically closed field `k` (with isogeny specializations in
`TauCeti.Algebra.AlgebraicGroup.Isogeny.Centralizer.ComponentGroup`):

* **Transport and trivial cases**:
  - `MulEquiv.cast` transports centralizer component groups across equalities of Lie algebra
    elements
    (`TauCeti.FiniteTypeCommHopfAlgCat.cast_centralizerComponentGroup_rationalComponentMap`).
  - `TauCeti.FiniteTypeCommHopfAlgCat.centralizerComponentGroupZeroEquiv`: `A(0) ≃* π₀(G)`.
* **Conjugation**:
  - `TauCeti.centralizerComponentGroupConjugationEquiv`: a rational point `g ∈ G(k)` induces
    `A(x) ≃* A(Ad(g) x)`, satisfying identity (`centralizerComponentGroupConjugationEquiv_one`),
    composition (`centralizerComponentGroupConjugationEquiv_trans`), inverse
    (`centralizerComponentGroupConjugationEquiv_symm`), and inner self-conjugation for
    `g ∈ C_G(x)(k)` (`centralizerComponentGroupConjugationEquiv_self_eq_conj`).
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
    particular when `toBialgHom f` and `dualCotangentMap (toBialgHom f)` are both injective:
    `centralizerComponentGroupMap_surjective_of_injective_coordinateMap_of_injective_differential`.
  - Exactness at `A_K(x)` (`TauCeti.mulExact_centralizerComponentGroupMap_of_faithfullyFlat`,
    `TauCeti.mulExact_centralizerComponentGroupMap_of_faithfullyFlat_of_le`, and their
    specializations): whenever `centralizerMap` is faithfully flat (in particular when
    `toBialgHom f` is faithfully flat with injective differential), the sequence
    `π₀(ker f ∩ C_K(x)) → A_K(x) → A_H(df(x))` is exact at `A_K(x)`, with `ker f ∩ C_K(x)` cut
    out by `CommHopfAlgCat.kernelHopfIdeal f.hom ⊔ centralizerHopfIdeal K x`, and injectivity is
    characterized by `(ker f ∩ C_K(x))(k) ⊆ C_K(x)°(k)`
    (`injective_centralizerComponentGroupMap_iff_of_faithfullyFlat`); when moreover
    `centralizerHopfIdeal K x ≤ kernelHopfIdeal f.hom` (in particular when `ker f` is central),
    this specializes to `π₀(ker f) → A_K(x) → A_H(df(x))` and characterizes injectivity by
    `(ker f)(k) ⊆ C_K(x)°(k)` (`injective_centralizerComponentGroupMap_iff_of_faithfullyFlat_of_le`
    and its central-kernel specialization).

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

/-- Transporting a rational-point component class along an equality of Lie algebra elements
preserves the underlying rational point. -/
@[simp]
theorem cast_centralizerComponentGroup_rationalComponentMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    {x y : Module.Dual k (Bialgebra.CotangentSpace k H)} (hxy : x = y)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) :
    _root_.cast (congrArg (fun z ↦ (centralizerHopfIdeal H z).ComponentGroup) hxy)
        ((centralizerHopfIdeal H x).rationalComponentMap g) =
      (centralizerHopfIdeal H y).rationalComponentMap ⟨g.val, hxy ▸ g.property⟩ := by
  subst hxy
  rfl

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
        (MulEquiv.cast (M := fun z ↦ (centralizerHopfIdeal H z).ComponentGroup)
          (by rw [map_one]; exact one_apply_eq_self x)) =
      MulEquiv.refl (centralizerHopfIdeal H x).ComponentGroup := by
  rw [MulEquiv.cast_comp (M := fun I : HopfIdeal k H ↦ I.ComponentGroup)
    (fun z ↦ centralizerHopfIdeal H z)]
  exact (HopfIdeal.componentGroupConjugationEquiv_trans_cast _ _ _ 1 _ _).trans
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
        (MulEquiv.cast (M := fun z ↦ (centralizerHopfIdeal H z).ComponentGroup)
          (by rw [map_mul]; exact mul_apply_eq_comp _ _ x)) := by
  rw [MulEquiv.cast_comp (M := fun I : HopfIdeal k H ↦ I.ComponentGroup)
    (fun z ↦ centralizerHopfIdeal H z)]
  exact (HopfIdeal.componentGroupConjugationEquiv_trans _ _ _ g g' _ _).trans
    (HopfIdeal.componentGroupConjugationEquiv_trans_cast _ _ _ (g' * g) _ _).symm

/-- The inverse of conjugation by `g` on centralizer component groups is conjugation by `g⁻¹`,
modulo canonical transport along `Ad(g⁻¹)(Ad(g) x) = x`. -/
@[simp]
theorem centralizerComponentGroupConjugationEquiv_symm
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    (centralizerComponentGroupConjugationEquiv x g).symm =
      (centralizerComponentGroupConjugationEquiv
          (Comodule.basePointsRepresentation (H := H) _ g x) g⁻¹).trans
        (MulEquiv.cast (M := fun z ↦ (centralizerHopfIdeal H z).ComponentGroup)
          (by
            rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]
            exact one_apply_eq_self x)) := by
  ext C
  obtain ⟨c, rfl⟩ := (centralizerHopfIdeal H
    (Comodule.basePointsRepresentation (H := H) _ g x)).rationalComponentMap_surjective C
  rw [MulEquiv.symm_apply_eq, MulEquiv.trans_apply,
    centralizerComponentGroupConjugationEquiv_rationalComponentMap,
    MulEquiv.cast_apply,
    cast_centralizerComponentGroup_rationalComponentMap H (by
      rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]
      exact one_apply_eq_self x),
    centralizerComponentGroupConjugationEquiv_rationalComponentMap]
  refine congrArg _ (Subtype.ext ?_)
  simp only [inv_inv, mul_assoc, mul_inv_cancel_left, mul_inv_cancel, mul_one]

/-- Self-conjugation by a rational point `g ∈ C_G(x)(k)` acts on `A(x)` by inner conjugation by
`[g] ∈ A(x)`. -/
theorem centralizerComponentGroupConjugationEquiv_self_eq_conj
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) :
    (centralizerComponentGroupConjugationEquiv x g.val).trans
        (MulEquiv.cast (M := fun z ↦ (centralizerHopfIdeal H z).ComponentGroup)
          ((mem_quotientPointsSubgroup_centralizerHopfIdeal_iff_basePointsRepresentation x
            g.val).mp g.property)) =
      MulAut.conj ((centralizerHopfIdeal H x).rationalComponentMap g) := by
  rw [MulEquiv.cast_comp (M := fun I : HopfIdeal k H ↦ I.ComponentGroup)
    (fun z ↦ centralizerHopfIdeal H z)]
  exact (HopfIdeal.componentGroupConjugationEquiv_trans_cast
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
        (f.hom.mapDomainQuotientPointsSubgroup
          ((toBialgHom f).map_centralizerHopfIdeal_le x) (CommAlgCat.of k k) c) :=
  HopfIdeal.componentGroupMap_rationalComponentMap _ _ f _ c

/-- Along the identity morphism, `centralizerComponentGroupMap` is the identity modulo canonical
transport along `d(id)(x) = x`. -/
@[simp]
theorem centralizerComponentGroupMap_id (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    (MulEquiv.cast (M := fun z ↦ (centralizerHopfIdeal H z).ComponentGroup)
          (dualCotangentMap_toBialgHom_id H x) : _ →* _).comp
        (centralizerComponentGroupMap (𝟙 H) x) =
      MonoidHom.id (centralizerHopfIdeal H x).ComponentGroup := by
  rw [← MulEquiv.toMonoidHom_eq_coe,
    MulEquiv.cast_comp (M := fun I : HopfIdeal k H ↦ I.ComponentGroup)
      (fun z ↦ centralizerHopfIdeal H z)]
  exact (HopfIdeal.cast_comp_componentGroupMap _ (centralizerHopfIdeal H x)
    (𝟙 H) _).trans (HopfIdeal.componentGroupMap_id (centralizerHopfIdeal H x) _)

/-- `centralizerComponentGroupMap` is contravariantly functorial in coordinate homomorphisms,
modulo canonical transport along `df(dg(x)) = d(g ∘ f)(x)`. -/
@[simp]
theorem centralizerComponentGroupMap_comp {L : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (g : K ⟶ L) (x : Module.Dual k (Bialgebra.CotangentSpace k L)) :
    (MulEquiv.cast (M := fun z ↦ (centralizerHopfIdeal H z).ComponentGroup)
          (dualCotangentMap_toBialgHom_comp f g x) : _ →* _).comp
        ((centralizerComponentGroupMap f (dualCotangentMap (toBialgHom g) x)).comp
          (centralizerComponentGroupMap g x)) =
      centralizerComponentGroupMap (f ≫ g) x := by
  rw [← MulEquiv.toMonoidHom_eq_coe, ← MonoidHom.comp_assoc, centralizerComponentGroupMap,
    centralizerComponentGroupMap,
    MulEquiv.cast_comp (M := fun I : HopfIdeal k H ↦ I.ComponentGroup)
      (fun z ↦ centralizerHopfIdeal H z),
    HopfIdeal.cast_comp_componentGroupMap, HopfIdeal.componentGroupMap_comp,
    centralizerComponentGroupMap]

/-- `centralizerComponentGroupMap` equals the component-group map of the coordinate arrow
`BialgHom.centralizerMap`. -/
theorem centralizerComponentGroupMap_eq_mapComponentGroup (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    centralizerComponentGroupMap f x =
      mapComponentGroup (ofHom ((toBialgHom f).centralizerMap x)) := by
  rw [centralizerComponentGroupMap, HopfIdeal.componentGroupMap_eq_mapComponentGroup,
    ofHom_centralizerMap]

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
    MulEquiv.cast (M := fun z ↦ (centralizerHopfIdeal H z).ComponentGroup)
        ((toBialgHom f).dualCotangentMap_basePointsRepresentation g x)
        (centralizerComponentGroupMap f (Comodule.basePointsRepresentation (H := K) _ g x)
          (centralizerComponentGroupConjugationEquiv x g C)) =
      centralizerComponentGroupConjugationEquiv (dualCotangentMap (toBialgHom f) x)
        (BialgHom.mapDomain (A := k) (toBialgHom f) g)
        (centralizerComponentGroupMap f x C) := by
  have hcast := DFunLike.congr_fun
    (HopfIdeal.cast_comp_componentGroupMap
      (congrArg (centralizerHopfIdeal H)
        ((toBialgHom f).dualCotangentMap_basePointsRepresentation g x))
      (centralizerHopfIdeal K (Comodule.basePointsRepresentation (H := K) _ g x)) f
      ((toBialgHom f).map_centralizerHopfIdeal_le
        (Comodule.basePointsRepresentation (H := K) _ g x)))
    (centralizerComponentGroupConjugationEquiv x g C)
  rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    ← MulEquiv.cast_comp (M := fun I : HopfIdeal k H ↦ I.ComponentGroup)
      (centralizerHopfIdeal H)] at hcast
  exact hcast.trans
    (HopfIdeal.componentGroupMap_componentGroupConjugationEquiv f
      ((toBialgHom f).map_centralizerHopfIdeal_le x) g
      (centralizerHopfIdeal_basePointsRepresentation (dualCotangentMap (toBialgHom f) x)
        (BialgHom.mapDomain (A := k) (toBialgHom f) g))
      (centralizerHopfIdeal_basePointsRepresentation x g) _ C)

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
theorem centralizerComponentGroupMap_surjective_of_injective_coordinateMap_of_injective_differential
    (f : H ⟶ K) (hf : Function.Injective (toBialgHom f))
    (hinj : Function.Injective (dualCotangentMap (toBialgHom f)))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Surjective (centralizerComponentGroupMap f x) :=
  centralizerComponentGroupMap_surjective f hf x
    ((toBialgHom f).map_centralizerHopfIdeal_eq_of_injective hinj x)

private theorem mulExact_centralizerComponentGroupMap_of_kernelIso (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (hf : ((toBialgHom f).centralizerMap x).toAlgHom.toRingHom.FaithfullyFlat)
    {I : HopfIdeal k K} (hle : centralizerHopfIdeal K x ≤ I)
    (iso : CommHopfAlgCat.quotient K.obj I ≅
      CommHopfAlgCat.quotient
        (CommHopfAlgCat.quotient K.obj (centralizerHopfIdeal K x))
        (CommHopfAlgCat.kernelHopfIdeal (ofHom ((toBialgHom f).centralizerMap x)).hom))
    (hcomp : CommHopfAlgCat.quotientMapOfLe K.obj hle ≫ iso.hom =
      CommHopfAlgCat.mkQuotient
        (CommHopfAlgCat.quotient K.obj (centralizerHopfIdeal K x))
        (CommHopfAlgCat.kernelHopfIdeal (ofHom ((toBialgHom f).centralizerMap x)).hom)) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K hle))
      (centralizerComponentGroupMap f x) := by
  let c : quotient H (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)) ⟶
      quotient K (centralizerHopfIdeal K x) :=
    ofHom ((toBialgHom f).centralizerMap x)
  have hex : Function.MulExact
      (mapComponentGroup (mkQuotient (quotient K (centralizerHopfIdeal K x))
        (CommHopfAlgCat.kernelHopfIdeal c.hom)))
      (centralizerComponentGroupMap f x) := by
    rw [centralizerComponentGroupMap_eq_mapComponentGroup]
    exact mulExact_mapComponentGroup_kernel c hf
  let _ := instGroupConnectedComponents
    (quotient (quotient K (centralizerHopfIdeal K x)) (CommHopfAlgCat.kernelHopfIdeal c.hom))
  exact mulExact_mapComponentGroup_of_comp_iso_hom _ _
    (ObjectProperty.isoMk _ iso) (ObjectProperty.hom_ext _ hcomp)
    (centralizerComponentGroupMap f x) hex

/-- Whenever the restricted coordinate map `BialgHom.centralizerMap` is faithfully flat, the
sequence `π₀(ker f ∩ C_K(x)) → A_K(x) → A_H(df(x))` is exact at `A_K(x)`, where `ker f ∩ C_K(x)`
is cut out by `CommHopfAlgCat.kernelHopfIdeal f.hom ⊔ centralizerHopfIdeal K x`. -/
theorem mulExact_centralizerComponentGroupMap_of_faithfullyFlat (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (hf : ((toBialgHom f).centralizerMap x).toAlgHom.toRingHom.FaithfullyFlat) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K
        (le_sup_right : centralizerHopfIdeal K x ≤
          CommHopfAlgCat.kernelHopfIdeal f.hom ⊔ centralizerHopfIdeal K x)))
      (centralizerComponentGroupMap f x) :=
  mulExact_centralizerComponentGroupMap_of_kernelIso f x hf le_sup_right
    (f.hom.kernelCentralizerMapIso x)
    (f.hom.quotientMapOfLe_comp_kernelCentralizerMapIso_hom x)

/-- For a faithfully flat homomorphism `f` with injective differential, the sequence
`π₀(ker f ∩ C_K(x)) → A_K(x) → A_H(df(x))` is exact at `A_K(x)`. -/
theorem mulExact_centralizerComponentGroupMap_of_faithfullyFlat_of_injective_differential
    (f : H ⟶ K) (hf : (toBialgHom f).toAlgHom.toRingHom.FaithfullyFlat)
    (hinj : Function.Injective (dualCotangentMap (toBialgHom f)))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K
        (le_sup_right : centralizerHopfIdeal K x ≤
          CommHopfAlgCat.kernelHopfIdeal f.hom ⊔ centralizerHopfIdeal K x)))
      (centralizerComponentGroupMap f x) :=
  mulExact_centralizerComponentGroupMap_of_faithfullyFlat f x
    ((toBialgHom f).faithfullyFlat_centralizerMap_of_injective_differential hf hinj x)

/-- Whenever `BialgHom.centralizerMap` is faithfully flat and `ker(f) ⊆ C_K(x)`, the sequence
`π₀(ker f) → A_K(x) → A_H(df(x))` is exact at `A_K(x)`. -/
theorem mulExact_centralizerComponentGroupMap_of_faithfullyFlat_of_le (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (hf : ((toBialgHom f).centralizerMap x).toAlgHom.toRingHom.FaithfullyFlat)
    (hle : centralizerHopfIdeal K x ≤ CommHopfAlgCat.kernelHopfIdeal f.hom) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K hle))
      (centralizerComponentGroupMap f x) :=
  mulExact_centralizerComponentGroupMap_of_kernelIso f x hf hle
    (f.hom.kernelCentralizerMapIsoOfLe x hle)
    (f.hom.quotientMapOfLe_comp_kernelCentralizerMapIsoOfLe_hom x hle)

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
  mulExact_centralizerComponentGroupMap_of_faithfullyFlat_of_le f x
    ((toBialgHom f).faithfullyFlat_centralizerMap_of_injective_differential hf hinj x)
    (centralizerHopfIdeal_le_of_isCentral hcent x)

/-- Whenever `BialgHom.centralizerMap` is faithfully flat, `A_K(x) → A_H(df(x))` is injective
if and only if every rational point of `ker f ∩ C_K(x)` lies in `C_K(x)°(k)`. -/
theorem injective_centralizerComponentGroupMap_iff_of_faithfullyFlat (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (hf : ((toBialgHom f).centralizerMap x).toAlgHom.toRingHom.FaithfullyFlat) :
    Function.Injective (centralizerComponentGroupMap f x) ↔
      CommHopfAlgCat.quotientPointsSubgroup K.obj
          (CommHopfAlgCat.kernelHopfIdeal f.hom ⊔ centralizerHopfIdeal K x)
          (CommAlgCat.of k k) ≤
        CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x).identityComponent
          (CommAlgCat.of k k) := by
  have hex := mulExact_centralizerComponentGroupMap_of_faithfullyFlat f x hf
  rw [← MonoidHom.ker_eq_bot_iff, hex.monoidHom_ker_eq,
    ← MonoidHom.range_comp_of_surjective _ _
      (CommHopfAlgCat.kernelHopfIdeal f.hom ⊔
        centralizerHopfIdeal K x).rationalComponentMap_surjective,
    MonoidHom.range_eq_bot_iff, MonoidHom.ext_iff]
  simp only [MonoidHom.comp_apply, MonoidHom.one_apply, IsConcreteLE.le_iff]
  exact (forall_congr' fun g ↦ by
    rw [mapComponentGroup_quotientMapOfLe_rationalComponentMap,
      (centralizerHopfIdeal K x).rationalComponentMap_eq_one_iff]).trans Subtype.forall

/-- Whenever `BialgHom.centralizerMap` is faithfully flat and `ker(f) ⊆ C_K(x)`,
`A_K(x) → A_H(df(x))` is injective if and only if every rational point of `ker f` lies in
`C_K(x)°(k)`. -/
theorem injective_centralizerComponentGroupMap_iff_of_faithfullyFlat_of_le (f : H ⟶ K)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (hf : ((toBialgHom f).centralizerMap x).toAlgHom.toRingHom.FaithfullyFlat)
    (hle : centralizerHopfIdeal K x ≤ CommHopfAlgCat.kernelHopfIdeal f.hom) :
    Function.Injective (centralizerComponentGroupMap f x) ↔
      CommHopfAlgCat.quotientPointsSubgroup K.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)
          (CommAlgCat.of k k) ≤
        CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x).identityComponent
          (CommAlgCat.of k k) := by
  rw [injective_centralizerComponentGroupMap_iff_of_faithfullyFlat f x hf,
    sup_eq_left.mpr hle]

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
  injective_centralizerComponentGroupMap_iff_of_faithfullyFlat_of_le f x
    ((toBialgHom f).faithfullyFlat_centralizerMap_of_injective_differential hf hinj x)
    (centralizerHopfIdeal_le_of_isCentral hcent x)

end Map

end TauCeti
