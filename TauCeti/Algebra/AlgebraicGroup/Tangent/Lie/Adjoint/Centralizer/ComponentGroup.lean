/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Action
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Exact
public import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.ComponentGroup
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Central
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Centralizer
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Conjugation

import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.ConnectedKernel
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
import TauCeti.RingTheory.Etale.Reduced

/-!
# Component groups of centralizers of Lie algebra elements

Let `G = Spec H` be an affine group of finite type over an algebraically closed field `k`, with
Lie algebra `𝔤`, and let `x ∈ 𝔤`. The component group of the centralizer is the finite group
`A(x) = π₀(C_G(x))`, written `(centralizerHopfIdeal H x).ComponentGroup`. By the general theory
of component groups of closed subgroups (`TauCeti.HopfIdeal.quotientMulEquivComponentGroup`)
it is `C_G(x)(k) ⧸ C_G(x)°(k)`, and `TauCeti.HopfIdeal.componentGroupInclusion` maps it to
`π₀(G)`.

This file develops both the scheme-theoretic foundations over an arbitrary field `k` and the
component-group API over an algebraically closed field:

* **Scheme-theoretic properties (any field `k`)**:
  - Every central closed subgroup (in particular the center `Z(G)` and the kernel of a central
    isogeny) is contained scheme-theoretically in `C_G(x)`
    (`TauCeti.centralizerHopfIdeal_le_of_isCentral`).
  - For any morphism `f : H ⟶ K`, the scheme-theoretic kernel of `C_K(x) → C_H(df(x))` is
    `ker(f) ∩ C_K(x)` (`TauCeti.kernelHopfIdeal_centralizerMap`), canonically isomorphic to
    `ker(f)` whenever `ker(f)` is central (`TauCeti.kernelCentralizerMapIsoOfIsCentral`).
* **Centralizer component groups `A(x)` (algebraically closed `k`)**:
  - Action and homomorphism descent from `C_G(x)(k)` to `A(x)` when `C_G(x)°(k)` acts trivially
    (`TauCeti.FiniteTypeCommHopfAlgCat.descCentralizerComponentGroupHom`,
    `TauCeti.FiniteTypeCommHopfAlgCat.centralizerComponentGroupActionHom`,
    `TauCeti.FiniteTypeCommHopfAlgCat.centralizerComponentGroupMulAction`).
  - Conjugation: a rational point `g` gives an isomorphism `A(x) ≃* A(Ad(g) x)`, sending the
    component of `c` to the component of `gcg⁻¹`
    (`TauCeti.centralizerComponentGroupConjugationEquiv`), acting by inner conjugation for
    `g ∈ C_G(x)(k)` fixing `x` (`TauCeti.centralizerComponentGroupConjugationEquiv_self_eq_conj`).
  - Homomorphisms: a homomorphism `φ : G' → G` of affine groups, given by its coordinate arrow
    `f : H ⟶ K` with `G' = Spec K`, maps `C_G'(x)` into `C_G(dφ x)` and so induces
    `A_G'(x) →* A_G(dφ x)` (`TauCeti.centralizerComponentGroupMap`), natural with respect to
    conjugation and the ambient component group, and surjective when the coordinate map of `φ` is
    injective and `C_G'(x)` is the full inverse image of `C_G(dφ x)`
    (`TauCeti.centralizerComponentGroupMap_surjective`), including separable isogenies and
    characteristic-zero isogenies (`TauCeti.centralizerComponentGroupMap_surjective_of_isIsogeny`).
  - Central-isogeny exact sequence: for separable (or characteristic-zero) isogenies `f`,
    exactness of `π₀(ker f ∩ C_K(x)) → A_K(x) → A_H(df(x)) → 1`, specializing for central
    isogenies to `π₀(ker f) → A_K(x) → A_H(df(x)) → 1`
    (`TauCeti.mulExact_centralizerComponentGroupMap_of_isCentral`) and characterizing injectivity
    by `(ker f)(k) ⊆ C_K(x)°(k)`
    (`TauCeti.injective_centralizerComponentGroupMap_iff_of_isCentral`).

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

section SchemeTheoretic

variable {k : Type u} [Field k]

/-- Every central closed subgroup scheme of `Spec H` is contained scheme-theoretically in the
centralizer of every Lie algebra element. In Hopf coordinates, `centralizerHopfIdeal H x ≤ I`. -/
theorem centralizerHopfIdeal_le_of_isCentral {H : Type u} [CommRing H] [HopfAlgebra k H]
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    {I : HopfIdeal k H} (hI : I.IsCentral)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    centralizerHopfIdeal H x ≤ I := by
  apply (HopfIdeal.le_iff_forall_quotientPointsSubgroup_le
    (H := _root_.CommHopfAlgCat.of k H) _ _).mpr
  intro A g hg
  rw [CommHopfAlgCat.mem_quotientPointsSubgroup_iff]
  have hpt : Derivation.pointInCounitAlgebra A g =
      AlgHom.mapValue (Bialgebra.CounitAlgebra.algEquivSelf k H A).symm.toAlgHom g := by
    apply WithConv.ofConv_injective
    ext y
    rw [Derivation.pointInCounitAlgebra_apply, AlgHom.mapValue_apply]
    simp only [AlgHom.comp_apply, AlgEquiv.coe_toAlgHom]
    exact (Bialgebra.CounitAlgebra.algEquivSelf_symm_apply (R := k) (A := H) (B := A)
      (g.ofConv y)).symm
  have hcent : HopfAlgebra.IsCentralPoint (Derivation.pointInCounitAlgebra A g) :=
    hpt ▸ (CommHopfAlgCat.isCentralPoint_of_mem_quotientPointsSubgroup
      (_root_.CommHopfAlgCat.of k H) I hI A hg).mapValue
      (Bialgebra.CounitAlgebra.algEquivSelf k H A).symm.toAlgHom
  have hle : (centralizerHopfIdeal H x).toIdeal ≤ RingHom.ker g.ofConv :=
    (centralizerHopfIdeal_le_ker_iff x g).mpr
      (Derivation.adDerivation_eq_self_of_isCentralPoint _ hcent)
  intro y hy
  exact hle (HopfIdeal.mem_toIdeal.mpr hy)

/-- The scheme-theoretic center `Z(G)` lies in the centralizer of every Lie algebra element. -/
theorem centralizerHopfIdeal_le_centerDefiningIdeal (H : _root_.CommHopfAlgCat.{u} k)
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    centralizerHopfIdeal H x ≤ CommHopfAlgCat.centerDefiningIdeal H :=
  centralizerHopfIdeal_le_of_isCentral (CommHopfAlgCat.isCentral_centerDefiningIdeal H) x

/-- For any morphism `f : H ⟶ K` of commutative Hopf algebras, the kernel Hopf ideal of the
induced centralizer morphism `C_K(x) → C_H(df(x))` is the image of `kernelHopfIdeal f` in
`O(C_K(x))`. -/
theorem kernelHopfIdeal_centralizerMap {H K : _root_.CommHopfAlgCat.{u} k}
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [Module.Finite k (Bialgebra.CotangentSpace k K)]
    (f : H ⟶ K) (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    CommHopfAlgCat.kernelHopfIdeal (_root_.CommHopfAlgCat.ofHom (f.hom.centralizerMap x)) =
      (CommHopfAlgCat.kernelHopfIdeal f).map
        (CommHopfAlgCat.mkQuotient K (centralizerHopfIdeal K x)).hom := by
  have hcomm :
      CommHopfAlgCat.mkQuotient H (centralizerHopfIdeal H (dualCotangentMap f.hom x)) ≫
          _root_.CommHopfAlgCat.ofHom (f.hom.centralizerMap x) =
        f ≫ CommHopfAlgCat.mkQuotient K (centralizerHopfIdeal K x) := by
    apply _root_.CommHopfAlgCat.hom_ext
    simpa only [_root_.CommHopfAlgCat.hom_comp, CommHopfAlgCat.hom_mkQuotient,
      _root_.CommHopfAlgCat.hom_ofHom] using f.hom.centralizerMap_comp_mkBialgHom x
  rw [← CommHopfAlgCat.kernelHopfIdeal_comp_of_surjective
      (CommHopfAlgCat.mkQuotient H (centralizerHopfIdeal H (dualCotangentMap f.hom x)))
      (CommHopfAlgCat.mkQuotient_surjective H _)
      (_root_.CommHopfAlgCat.ofHom (f.hom.centralizerMap x)),
    hcomm, CommHopfAlgCat.kernelHopfIdeal_comp]

/-- Pulling back the kernel of `C_K(x) → C_H(df(x))` to `K` gives the scheme-theoretic intersection
`ker(f) ∩ C_K(x)` (`kernelHopfIdeal f ⊔ centralizerHopfIdeal K x`). -/
theorem comapOfSurjective_kernelHopfIdeal_centralizerMap {H K : _root_.CommHopfAlgCat.{u} k}
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [Module.Finite k (Bialgebra.CotangentSpace k K)]
    (f : H ⟶ K) (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    (CommHopfAlgCat.kernelHopfIdeal
        (_root_.CommHopfAlgCat.ofHom (f.hom.centralizerMap x))).comapOfSurjective
        (CommHopfAlgCat.mkQuotient K (centralizerHopfIdeal K x)).hom
        (CommHopfAlgCat.mkQuotient_surjective K _) =
      CommHopfAlgCat.kernelHopfIdeal f ⊔ centralizerHopfIdeal K x := by
  rw [kernelHopfIdeal_centralizerMap, HopfIdeal.comapOfSurjective_map]
  have hker :
      HopfIdeal.kerOfSurjective (CommHopfAlgCat.mkQuotient K (centralizerHopfIdeal K x)).hom
        (CommHopfAlgCat.mkQuotient_surjective K _) = centralizerHopfIdeal K x := by
    simpa only [CommHopfAlgCat.hom_mkQuotient] using
      HopfIdeal.kerOfSurjective_mkBialgHom (centralizerHopfIdeal K x)
  rw [hker]

/-- When `ker(f)` is central, the scheme-theoretic kernel of `C_K(x) → C_H(df(x))` is canonically
isomorphic to `ker(f)`. -/
noncomputable def kernelCentralizerMapIsoOfIsCentral {H K : _root_.CommHopfAlgCat.{u} k}
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [Module.Finite k (Bialgebra.CotangentSpace k K)]
    (f : H ⟶ K) (hf : (CommHopfAlgCat.kernelHopfIdeal f).IsCentral)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    CommHopfAlgCat.quotient K (CommHopfAlgCat.kernelHopfIdeal f) ≅
      CommHopfAlgCat.quotient
        (CommHopfAlgCat.quotient K (centralizerHopfIdeal K x))
        (CommHopfAlgCat.kernelHopfIdeal
          (_root_.CommHopfAlgCat.ofHom (f.hom.centralizerMap x))) :=
  ((CommHopfAlgCat.mkQuotient K (centralizerHopfIdeal K x)).quotientIsoQuotientQuotient rfl
      (centralizerHopfIdeal_le_of_isCentral hf x)) ≪≫
    eqToIso (congrArg (CommHopfAlgCat.quotient _) (kernelHopfIdeal_centralizerMap f x).symm)

/-- The canonical isomorphism `ker(f) ≅ ker(C_K(x) → C_H(df(x)))` identifies the closed immersion
`ker(f) ↪ C_K(x)` with the kernel immersion `ker(centralizerMap) ↪ C_K(x)`. -/
theorem quotientMapOfLe_comp_kernelCentralizerMapIsoOfIsCentral_hom
    {H K : _root_.CommHopfAlgCat.{u} k}
    [Module.Finite k (Bialgebra.CotangentSpace k H)]
    [Module.Finite k (Bialgebra.CotangentSpace k K)]
    (f : H ⟶ K) (hf : (CommHopfAlgCat.kernelHopfIdeal f).IsCentral)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    CommHopfAlgCat.quotientMapOfLe K (centralizerHopfIdeal_le_of_isCentral hf x) ≫
        (kernelCentralizerMapIsoOfIsCentral f hf x).hom =
      CommHopfAlgCat.mkQuotient (CommHopfAlgCat.quotient K (centralizerHopfIdeal K x))
        (CommHopfAlgCat.kernelHopfIdeal
          (_root_.CommHopfAlgCat.ofHom (f.hom.centralizerMap x))) := by
  apply CommHopfAlgCat.mkQuotient_hom_ext
  rw [← Category.assoc, CommHopfAlgCat.mkQuotient_comp_quotientMapOfLe,
    kernelCentralizerMapIsoOfIsCentral, Iso.trans_hom, ← Category.assoc,
    CommHopfAlgCat.Hom.mkQuotient_comp_quotientIsoQuotientQuotient_hom, Category.assoc,
    eqToIso.hom, CommHopfAlgCat.mkQuotient_comp_eqToHom (kernelHopfIdeal_centralizerMap f x)]

end SchemeTheoretic

namespace FiniteTypeCommHopfAlgCat

variable {k : Type u} [Field k] [IsAlgClosed k]

section ActionDescent

/-- Descend a homomorphism `C_G(x)(k) →* M` vanishing on `C_G(x)°(k)` to `A(x)`. -/
noncomputable def descCentralizerComponentGroupHom (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
        (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x).identityComponent
          (CommAlgCat.of k k) →
      φ g = 1) :
    (centralizerHopfIdeal H x).ComponentGroup →* M :=
  descSubgroupComponentGroupHom H (centralizerHopfIdeal H x) φ hφ

/-- The descended homomorphism on `A(x)` agrees with `φ` on `C_G(x)(k)`. -/
@[simp]
theorem descCentralizerComponentGroupHom_rationalComponentMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
        (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x).identityComponent
          (CommAlgCat.of k k) →
      φ g = 1)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) :
    descCentralizerComponentGroupHom H x φ hφ
        ((centralizerHopfIdeal H x).rationalComponentMap g) = φ g :=
  descSubgroupComponentGroupHom_rationalComponentMap H (centralizerHopfIdeal H x) φ hφ g

/-- A homomorphism out of `A(x)` is uniquely determined by its values on `C_G(x)(k)`. -/
theorem descCentralizerComponentGroupHom_unique (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
        (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x).identityComponent
          (CommAlgCat.of k k) →
      φ g = 1)
    (ψ : (centralizerHopfIdeal H x).ComponentGroup →* M)
    (hψ : ∀ g, ψ ((centralizerHopfIdeal H x).rationalComponentMap g) = φ g) :
    ψ = descCentralizerComponentGroupHom H x φ hφ :=
  descSubgroupComponentGroupHom_unique H (centralizerHopfIdeal H x) φ hφ ψ hψ

/-- The kernel of the descended homomorphism on `A(x)` is the image of `ker φ` under
`HopfIdeal.rationalComponentMap`. -/
theorem ker_descCentralizerComponentGroupHom (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) {M : Type*} [Monoid M]
    (φ : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k) →* M)
    (hφ : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
        (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x).identityComponent
          (CommAlgCat.of k k) →
      φ g = 1) :
    (descCentralizerComponentGroupHom H x φ hφ).ker =
      φ.ker.map (centralizerHopfIdeal H x).rationalComponentMap :=
  ker_descSubgroupComponentGroupHom H (centralizerHopfIdeal H x) φ hφ

/-- Descend a `C_G(x)(k)`-action on `X` whose restriction to `C_G(x)°(k)` is trivial to a
permutation representation of `A(x)`. -/
noncomputable def centralizerComponentGroupActionHom (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
        (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x).identityComponent
          (CommAlgCat.of k k) →
      ∀ y : X, g • y = y) :
    (centralizerHopfIdeal H x).ComponentGroup →* Equiv.Perm X :=
  subgroupComponentGroupActionHom H (centralizerHopfIdeal H x) X htriv

/-- The descended `A(x)`-action agrees with the `C_G(x)(k)`-action. -/
@[simp]
theorem centralizerComponentGroupActionHom_rationalComponentMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
        (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x).identityComponent
          (CommAlgCat.of k k) →
      ∀ y : X, g • y = y)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) (y : X) :
    centralizerComponentGroupActionHom H x X htriv
        ((centralizerHopfIdeal H x).rationalComponentMap g) y = g • y :=
  subgroupComponentGroupActionHom_rationalComponentMap H (centralizerHopfIdeal H x) X htriv g y

/-- The descended `MulAction` of `A(x)` on `X` from a `C_G(x)(k)`-action trivial on
`C_G(x)°(k)`. -/
noncomputable abbrev centralizerComponentGroupMulAction (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
        (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x).identityComponent
          (CommAlgCat.of k k) →
      ∀ y : X, g • y = y) :
    MulAction (centralizerHopfIdeal H x).ComponentGroup X :=
  MulAction.compHom X (centralizerComponentGroupActionHom H x X htriv)

/-- The orbits of the descended `A(x)`-action coincide with the `C_G(x)(k)`-orbits. -/
theorem orbit_centralizerComponentGroupMulAction (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
        (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x).identityComponent
          (CommAlgCat.of k k) →
      ∀ y : X, g • y = y) (y : X) :
    letI := centralizerComponentGroupMulAction H x X htriv
    MulAction.orbit (centralizerHopfIdeal H x).ComponentGroup y =
      MulAction.orbit (CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
        (CommAlgCat.of k k)) y :=
  orbit_subgroupComponentGroupMulAction H (centralizerHopfIdeal H x) X htriv y

/-- The stabilizer in `A(x)` of a point is the image of its `C_G(x)(k)`-stabilizer. -/
theorem stabilizer_centralizerComponentGroupMulAction (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
        (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x).identityComponent
          (CommAlgCat.of k k) →
      ∀ y : X, g • y = y) (y : X) :
    letI := centralizerComponentGroupMulAction H x X htriv
    MulAction.stabilizer (centralizerHopfIdeal H x).ComponentGroup y =
      (MulAction.stabilizer
        (CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
          (CommAlgCat.of k k)) y).map (centralizerHopfIdeal H x).rationalComponentMap :=
  stabilizer_subgroupComponentGroupMulAction H (centralizerHopfIdeal H x) X htriv y

/-- The fixed points of the descended `A(x)`-action coincide with the `C_G(x)(k)`-fixed points. -/
theorem fixedPoints_centralizerComponentGroupMulAction (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) (X : Type*)
    [MulAction (CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) X]
    (htriv : ∀ g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
        (CommAlgCat.of k k),
      (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) ∈
        CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x).identityComponent
          (CommAlgCat.of k k) →
      ∀ y : X, g • y = y) :
    letI := centralizerComponentGroupMulAction H x X htriv
    MulAction.fixedPoints (centralizerHopfIdeal H x).ComponentGroup X =
      MulAction.fixedPoints
        (CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
          (CommAlgCat.of k k)) X :=
  fixedPoints_subgroupComponentGroupMulAction H (centralizerHopfIdeal H x) X htriv

end ActionDescent

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

/-- If `G` is connected, the inclusion `A(x) → π₀(G)` is trivial (even though `A(x)` itself may
be nontrivial). -/
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

/-- Self-conjugation by a rational point `g ∈ C_G(x)(k)` fixing `x` acts on `A(x)` by inner
conjugation by `[g] ∈ A(x)`. -/
theorem centralizerComponentGroupConjugationEquiv_self_eq_conj
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k))
    (hx : Comodule.basePointsRepresentation (H := H) _ g.val x = x) :
    (centralizerComponentGroupConjugationEquiv x g.val).trans
        (centralizerComponentGroupEquivOfEq H hx) =
      MulAut.conj ((centralizerHopfIdeal H x).rationalComponentMap g) := by
  ext C
  obtain ⟨h, rfl⟩ := (centralizerHopfIdeal H x).rationalComponentMap_surjective C
  rw [MulEquiv.trans_apply, centralizerComponentGroupConjugationEquiv_rationalComponentMap,
    centralizerComponentGroupEquivOfEq_rationalComponentMap, MulAut.conj_apply,
    ← map_inv, ← map_mul, ← map_mul]
  rfl

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

/-- `centralizerComponentGroupMap` commutes with the inclusions `A_K(x) → π₀(K)` and
`A_H(df(x)) → π₀(H)` into the ambient component groups. -/
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
    (hxy : dualCotangentMap (toBialgHom f)
        (Comodule.basePointsRepresentation (H := K) _ g x) =
      Comodule.basePointsRepresentation (H := H) _
        (BialgHom.mapDomain (A := k) (toBialgHom f) g)
        (dualCotangentMap (toBialgHom f) x))
    (C : (centralizerHopfIdeal K x).ComponentGroup) :
    centralizerComponentGroupEquivOfEq H hxy
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
  congr 1
  exact Subtype.ext (by simp [map_mul, map_inv])

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

/-- An isogeny with injective differential induces a surjection `A_K(x) ↠ A_H(df(x))`. -/
theorem centralizerComponentGroupMap_surjective_of_injective_differential (f : H ⟶ K)
    (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hinj : Function.Injective (dualCotangentMap (toBialgHom f)))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Surjective (centralizerComponentGroupMap f x) :=
  centralizerComponentGroupMap_surjective f hf.injective x
    ((toBialgHom f).map_centralizerHopfIdeal_eq_of_injective hinj x)

/-- An isogeny with étale kernel induces a surjection `A_K(x) ↠ A_H(df(x))`. -/
theorem centralizerComponentGroupMap_surjective_of_etaleKernel (f : H ⟶ K)
    (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hker : Algebra.Etale k (K ⧸ (CommHopfAlgCat.kernelHopfIdeal f.hom).toIdeal))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Surjective (centralizerComponentGroupMap f x) :=
  centralizerComponentGroupMap_surjective_of_injective_differential f hf
    (hf.dualCotangentMap_bijective_of_etaleKernel hker).injective x

/-- In characteristic zero, an isogeny `φ : G' → G` induces a surjection
`π₀(C_G'(x)) →* π₀(C_G(dφ x))` of centralizer component groups. This includes central isogenies
of semisimple groups, for which the map need not be injective. -/
theorem centralizerComponentGroupMap_surjective_of_isIsogeny [CharZero k] (f : H ⟶ K)
    (hf : CommHopfAlgCat.IsIsogeny f.hom) (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Surjective (centralizerComponentGroupMap f x) :=
  centralizerComponentGroupMap_surjective f hf.injective x
    (hf.map_centralizerHopfIdeal_of_charZero x)

/-- For an isogeny `f` with injective differential, the sequence
`π₀(ker f ∩ C_K(x)) → A_K(x) → A_H(df(x))` is exact. -/
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
      (centralizerComponentGroupMap f x) := by
  intro c
  have heq : centralizerComponentGroupMap f x = mapComponentGroup c := by
    ext C
    obtain ⟨g, rfl⟩ := (centralizerHopfIdeal K x).rationalComponentMap_surjective C
    obtain ⟨q, rfl⟩ := (CommHopfAlgCat.quotientPointsSubgroupIso K.obj (centralizerHopfIdeal K x)
      (CommAlgCat.of k k)).groupIsoToMulEquiv.surjective g
    have hqeq :
        (CommHopfAlgCat.quotientPointsSubgroupIso K.obj (centralizerHopfIdeal K x)
          (CommAlgCat.of k k)).groupIsoToMulEquiv q =
        ⟨CommHopfAlgCat.quotientPointsHom K.obj (centralizerHopfIdeal K x) (CommAlgCat.of k k) q,
          CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup K.obj _ _ q⟩ :=
      CommHopfAlgCat.quotientPointsSubgroupIso_hom_apply K.obj _ _ q
    rw [hqeq, HopfIdeal.rationalComponentMap_quotientPointsHom,
      mapComponentGroup_rationalComponentMap]
    rw [← HopfIdeal.rationalComponentMap_quotientPointsHom (centralizerHopfIdeal K x) q,
      centralizerComponentGroupMap_rationalComponentMap, HopfIdeal.rationalComponentMap_apply]
    congr 1
    refine (CommHopfAlgCat.liftQuotientPoint_eq_iff H.obj _ (CommAlgCat.of k k) _ _ _).mpr ?_
    apply WithConv.ofConv_injective
    ext a
    rw [CommHopfAlgCat.quotientPointsHom_apply_apply, Ideal.Quotient.mkₐ_eq_mk,
      BialgHom.mapDomain_apply_apply, BialgHom.mapDomain_apply_apply,
      CommHopfAlgCat.quotientPointsHom_apply_apply, Ideal.Quotient.mkₐ_eq_mk]
    change _ = q.ofConv (((toBialgHom f).centralizerMap x) (Ideal.Quotient.mk _ a))
    rw [BialgHom.centralizerMap_mk]
  rw [heq]
  exact mulExact_mapComponentGroup_kernel c (hf.centralizerMap_of_injective hinj x).faithfullyFlat

/-- **Central-isogeny exact sequence on centralizer component groups.**
For an isogeny `f` with injective differential and central kernel, the natural sequence
`π₀(ker f) → A_K(x) → A_H(df(x)) → 1` is exact at `A_K(x)` (and surjective at `A_H(df(x))` by
`centralizerComponentGroupMap_surjective_of_injective_differential`). -/
theorem mulExact_centralizerComponentGroupMap_of_isCentral (f : H ⟶ K)
    (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hinj : Function.Injective (dualCotangentMap (toBialgHom f)))
    (hcent : (CommHopfAlgCat.kernelHopfIdeal f.hom).IsCentral)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K (centralizerHopfIdeal_le_of_isCentral hcent x)))
      (centralizerComponentGroupMap f x) := by
  let c : quotient H (centralizerHopfIdeal H (dualCotangentMap (toBialgHom f) x)) ⟶
      quotient K (centralizerHopfIdeal K x) :=
    ofHom ((toBialgHom f).centralizerMap x)
  have hex := mulExact_centralizerComponentGroupMap_of_injective_differential f hf hinj x
  let _ := instGroupConnectedComponents
    (quotient (quotient K (centralizerHopfIdeal K x)) (CommHopfAlgCat.kernelHopfIdeal c.hom))
  let iso : quotient K (CommHopfAlgCat.kernelHopfIdeal f.hom) ≅
      quotient (quotient K (centralizerHopfIdeal K x)) (CommHopfAlgCat.kernelHopfIdeal c.hom) :=
    ObjectProperty.isoMk _ (kernelCentralizerMapIsoOfIsCentral f.hom hcent x)
  have hcomp :
      quotientMapOfLe K (centralizerHopfIdeal_le_of_isCentral hcent x) ≫ iso.hom =
        mkQuotient (quotient K (centralizerHopfIdeal K x))
          (CommHopfAlgCat.kernelHopfIdeal c.hom) :=
    ObjectProperty.hom_ext _
      (quotientMapOfLe_comp_kernelCentralizerMapIsoOfIsCentral_hom f.hom hcent x)
  have hmap :
      mapComponentGroup (mkQuotient (quotient K (centralizerHopfIdeal K x))
          (CommHopfAlgCat.kernelHopfIdeal c.hom)) =
        (mapComponentGroup (quotientMapOfLe K (centralizerHopfIdeal_le_of_isCentral hcent x))).comp
          (mapComponentGroup iso.hom) := by
    rw [← hcomp, mapComponentGroup_comp]
  have hiso_surj : Function.Surjective (mapComponentGroup iso.hom) := by
    intro D
    have hcomp_id : (mapComponentGroup iso.hom).comp (mapComponentGroup iso.inv) =
        MonoidHom.id _ := by
      rw [← mapComponentGroup_comp, iso.hom_inv_id, mapComponentGroup_id]
    exact ⟨mapComponentGroup iso.inv D, DFunLike.congr_fun hcomp_id D⟩
  intro C
  rw [hex C]
  constructor
  · rintro ⟨D, rfl⟩
    exact ⟨mapComponentGroup iso.hom D, (DFunLike.congr_fun hmap D).symm⟩
  · rintro ⟨E, rfl⟩
    obtain ⟨D, rfl⟩ := hiso_surj E
    exact ⟨D, DFunLike.congr_fun hmap D⟩

/-- Characteristic-zero central-isogeny exact sequence `π₀(ker f) → A_K(x) → A_H(df(x)) → 1`. -/
theorem mulExact_centralizerComponentGroupMap_of_isCentralIsogeny_of_charZero [CharZero k]
    (f : H ⟶ K) (hf : CommHopfAlgCat.IsCentralIsogeny f.hom)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K
        (centralizerHopfIdeal_le_of_isCentral hf.isCentral_kernelHopfIdeal x)))
      (centralizerComponentGroupMap f x) := by
  let Q := CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)
  have het : Algebra.Etale k Q :=
    algebraEtale_iff_finite_and_isReduced.mpr
      ⟨CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal hf.isIsogeny.finite,
        HopfAlgebra.isReduced_of_charZero k Q⟩
  exact mulExact_centralizerComponentGroupMap_of_isCentral f hf.isIsogeny
    (hf.isIsogeny.dualCotangentMap_bijective_of_etaleKernel het).injective
    hf.isCentral_kernelHopfIdeal x

/-- In characteristic zero, every isogeny from a geometrically connected affine group is central
and therefore induces the exact sequence `π₀(ker f) → A_K(x) → A_H(df(x)) → 1`. -/
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

/-- For a central isogeny with injective differential, `A_K(x) → A_H(df(x))` is injective (hence
an isomorphism) if and only if every rational point of `ker f` lies in `C_K(x)°(k)`. -/
theorem injective_centralizerComponentGroupMap_iff_of_isCentral (f : H ⟶ K)
    (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hinj : Function.Injective (dualCotangentMap (toBialgHom f)))
    (hcent : (CommHopfAlgCat.kernelHopfIdeal f.hom).IsCentral)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Injective (centralizerComponentGroupMap f x) ↔
      CommHopfAlgCat.quotientPointsSubgroup K.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)
          (CommAlgCat.of k k) ≤
        CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x).identityComponent
          (CommAlgCat.of k k) := by
  have hex := mulExact_centralizerComponentGroupMap_of_isCentral f hf hinj hcent x
  rw [injective_iff_map_eq_one]
  constructor
  · intro hinjC g hg
    let gK : CommHopfAlgCat.quotientPointsSubgroup K.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)
        (CommAlgCat.of k k) := ⟨g, hg⟩
    let gC : CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x)
        (CommAlgCat.of k k) :=
      ⟨g, CommHopfAlgCat.quotientPointsSubgroup_le_of_le K.obj
        (centralizerHopfIdeal_le_of_isCentral hcent x) _ hg⟩
    have hmap : centralizerComponentGroupMap f x
        ((centralizerHopfIdeal K x).rationalComponentMap gC) = 1 := by
      rw [← mapComponentGroup_quotientMapOfLe_rationalComponentMap K
        (centralizerHopfIdeal_le_of_isCentral hcent x) gK]
      exact (hex _).mpr ⟨(CommHopfAlgCat.kernelHopfIdeal f.hom).rationalComponentMap gK, rfl⟩
    exact ((centralizerHopfIdeal K x).rationalComponentMap_eq_one_iff gC).mp (hinjC _ hmap)
  · intro hle C hC
    obtain ⟨D, rfl⟩ := (hex C).mp hC
    obtain ⟨gK, rfl⟩ := (CommHopfAlgCat.kernelHopfIdeal f.hom).rationalComponentMap_surjective D
    rw [mapComponentGroup_quotientMapOfLe_rationalComponentMap]
    exact ((centralizerHopfIdeal K x).rationalComponentMap_eq_one_iff _).mpr (hle gK.property)

end Map

end TauCeti
