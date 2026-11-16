/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Center.Basic
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Conjugation
public import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.Exact
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Central
public import TauCeti.Algebra.AlgebraicGroup.Isogeny.Centralizer
public import TauCeti.Algebra.AlgebraicGroup.Tangent.Lie.Adjoint.Centralizer.Conjugation

import TauCeti.Algebra.AlgebraicGroup.Connected.ComponentGroup.ConnectedKernel
import TauCeti.Algebra.AlgebraicGroup.HopfIdeal.Points.Kernel
import TauCeti.Algebra.AlgebraicGroup.Tangent.FiniteType
import TauCeti.RingTheory.Etale.Reduced

/-!
# Centralizer component groups

For a finite-type affine group `G = Spec H` over an algebraically closed field `k` and an element
`x` of its Lie algebra `𝔤 = (𝔪/𝔪²)*`, the centralizer `C_G(x) = Spec (H ⧸ centralizerHopfIdeal H x)`
is a closed subgroup scheme of `G`, distinct in general from its Lie algebra `Lie(C_G(x))`, its
identity component `C_G(x)°`, and its finite component group
`A_G(x) := π₀(C_G(x)) = C_G(x)(k) / C_G(x)°(k)`.

This file develops both the scheme-theoretic foundations over an arbitrary field `k` and the
component-group API over an algebraically closed field:

* **Scheme-theoretic properties (any field `k`)**:
  - Every central closed subgroup (in particular the center `Z(G)` and the kernel of a central
    isogeny) is contained scheme-theoretically in `C_G(x)`.
  - For any morphism `f : H ⟶ K`, the scheme-theoretic kernel of `C_K(x) → C_H(df(x))` is
    `ker(f) ∩ C_K(x)`, canonically isomorphic to `ker(f)` whenever `ker(f)` is central.
* **Centralizer component groups `A_G(x)` (algebraically closed `k`)**:
  - Action and homomorphism descent from `C_G(x)(k)` to `A_G(x)` when `C_G(x)°(k)` acts trivially.
  - Conjugation isomorphisms `A_G(x) ≃* A_G(Ad(g) x)`, functorial in `g`, compatible with `π₀(G)`,
    inner on `C_G(x)(k)`, and trivial on `C_G(x)°(k)`.
  - Induced homomorphisms `A_K(x) →* A_H(df(x))` for arbitrary morphisms `f : H ⟶ K`, natural with
    respect to conjugation and the ambient component group.
  - For separable (or characteristic-zero) isogenies `f`, surjectivity of `A_K(x) → A_H(df(x))` and
    exactness of `π₀(ker f ∩ C_K(x)) → A_K(x) → A_H(df(x)) → 1`, specializing for central isogenies
    to the exact sequence `π₀(ker f) → A_K(x) → A_H(df(x)) → 1` and characterizing injectivity by
    `(ker f)(k) ⊆ C_K(x)°(k)`.

## Main declarations

* `TauCeti.centralizerHopfIdeal_le_of_isCentral` and `TauCeti.kernelHopfIdeal_centralizerMap`:
  scheme-theoretic centralizer properties over any field.
* `TauCeti.FiniteTypeCommHopfAlgCat.centralizerComponentGroup`,
  `TauCeti.FiniteTypeCommHopfAlgCat.centralizerComponentMap`, and
  `TauCeti.FiniteTypeCommHopfAlgCat.centralizerComponentGroupEquivQuotient`: the finite group
  `A_G(x) = π₀(C_G(x)) ≃* C_G(x)(k) / C_G(x)°(k)`.
* `TauCeti.FiniteTypeCommHopfAlgCat.descCentralizerComponentGroupHom`,
  `TauCeti.FiniteTypeCommHopfAlgCat.centralizerComponentGroupActionHom`, and
  `TauCeti.FiniteTypeCommHopfAlgCat.centralizerComponentGroupMulAction`: homomorphism and action
  descent from `C_G(x)(k)` to `A_G(x)`.
* `TauCeti.FiniteTypeCommHopfAlgCat.centralizerComponentGroupConjugationEquiv`: conjugation
  isomorphism `A_G(x) ≃* A_G(Ad(g) x)`.
* `TauCeti.FiniteTypeCommHopfAlgCat.mapCentralizerComponentGroup`,
  `TauCeti.FiniteTypeCommHopfAlgCat.mulExact_mapCentralizerComponentGroup_of_isCentral`, and
  `TauCeti.FiniteTypeCommHopfAlgCat.injective_mapCentralizerComponentGroup_iff_of_isCentral`:
  functoriality and central-isogeny exact sequence for centralizer component groups.

## References

* D. H. Collingwood and W. M. McGovern, *Nilpotent Orbits in Semisimple Lie Algebras*,
  Van Nostrand Reinhold, 1993, §6.1.
* J. C. Jantzen, *Nilpotent Orbits in Representation Theory*, Progress in Mathematics 228,
  Birkhäuser, 2004, §3.
* J. S. Milne, *Algebraic Groups* (2017), Chapters 5, 10, and 18.
-/

public section

open CategoryTheory WithConv Derivation

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

/-- The centralizer component group `A_G(x) = π₀(C_G(x))` of an element `x` of the Lie algebra of a
finite-type affine group `G = Spec H`. Defined as `ConnectedComponents (PrimeSpectrum (H ⧸ I))`
where `I = centralizerHopfIdeal H x`, with dedicated `Group` and `Finite` instances so typeclass
synthesis succeeds directly even when `H` is instantiated with a concrete Hopf algebra. -/
@[expose] noncomputable def centralizerComponentGroup (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) : Type u :=
  ConnectedComponents (PrimeSpectrum (quotient H (centralizerHopfIdeal H x)))

/-- The group structure on the centralizer component group `A_G(x)`, definitionally equal to the
component-group structure on `π₀(C_G(x))`. -/
noncomputable instance instGroupCentralizerComponentGroup
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    Group (centralizerComponentGroup H x) :=
  instGroupConnectedComponents (quotient H (centralizerHopfIdeal H x))

/-- The centralizer component group `A_G(x)` of an element of the Lie algebra of a finite-type
affine group is finite. -/
instance instFiniteCentralizerComponentGroup
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    Finite (centralizerComponentGroup H x) :=
  instFiniteConnectedComponents (quotient H (centralizerHopfIdeal H x))

/-- The canonical rational-point homomorphism `C_G(x)(k) →* A_G(x)`. -/
@[expose] noncomputable def centralizerComponentMap (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x) (CommAlgCat.of k k) →*
      centralizerComponentGroup H x :=
  subgroupComponentMap H (centralizerHopfIdeal H x)

/-- Every element of `A_G(x)` is represented by a rational point of `C_G(x)`. -/
theorem centralizerComponentMap_surjective (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    Function.Surjective (centralizerComponentMap H x) :=
  subgroupComponentMap_surjective H (centralizerHopfIdeal H x)

/-- A rational point of `C_G(x)` maps to `1 ∈ A_G(x)` if and only if it lies in `C_G(x)°(k)`. -/
@[simp]
theorem centralizerComponentMap_eq_one_iff (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) :
    centralizerComponentMap H x g = 1 ↔
      g.1 ∈ CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H x).identityComponent (CommAlgCat.of k k) :=
  subgroupComponentMap_eq_one_iff H (centralizerHopfIdeal H x) g

/-- The kernel of `C_G(x)(k) →* A_G(x)` is the identity-component subgroup `C_G(x)°(k)`. -/
theorem ker_centralizerComponentMap (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    (centralizerComponentMap H x).ker =
      (CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x).identityComponent
        (CommAlgCat.of k k)).subgroupOf
        (CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
          (CommAlgCat.of k k)) :=
  ker_subgroupComponentMap H (centralizerHopfIdeal H x)

/-- Evaluating `centralizerComponentMap` on an included quotient point agrees with
`rationalComponentMap`. -/
@[simp]
theorem centralizerComponentMap_quotientPointsHom
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (q : HopfAlgebra.points (R := k) (H := quotient H (centralizerHopfIdeal H x))
      (CommAlgCat.of k k)) :
    centralizerComponentMap H x
        ⟨CommHopfAlgCat.quotientPointsHom H.obj (centralizerHopfIdeal H x) (CommAlgCat.of k k) q,
          CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H.obj _ _ q⟩ =
      rationalComponentMap (quotient H (centralizerHopfIdeal H x)) q :=
  subgroupComponentMap_quotientPointsHom H (centralizerHopfIdeal H x) q

/-- The canonical isomorphism `C_G(x)(k) / C_G(x)°(k) ≃* A_G(x)`. -/
noncomputable def centralizerComponentGroupEquivQuotient
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H)) :
    CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x) (CommAlgCat.of k k) ⧸
        ((CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x).identityComponent
          (CommAlgCat.of k k)).subgroupOf
          (CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
            (CommAlgCat.of k k))) ≃*
      centralizerComponentGroup H x :=
  subgroupComponentGroupEquivQuotient H (centralizerHopfIdeal H x)

section ActionDescent

/-- Descend a homomorphism `C_G(x)(k) →* M` vanishing on `C_G(x)°(k)` to `A_G(x)`. -/
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
    centralizerComponentGroup H x →* M :=
  descSubgroupComponentGroupHom H (centralizerHopfIdeal H x) φ hφ

/-- The descended homomorphism on `A_G(x)` agrees with `φ` on `C_G(x)(k)`. -/
@[simp]
theorem descCentralizerComponentGroupHom_centralizerComponentMap
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
    descCentralizerComponentGroupHom H x φ hφ (centralizerComponentMap H x g) = φ g :=
  descSubgroupComponentGroupHom_subgroupComponentMap H (centralizerHopfIdeal H x) φ hφ g

/-- A homomorphism out of `A_G(x)` is uniquely determined by its values on `C_G(x)(k)`. -/
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
    (ψ : centralizerComponentGroup H x →* M)
    (hψ : ∀ g, ψ (centralizerComponentMap H x g) = φ g) :
    ψ = descCentralizerComponentGroupHom H x φ hφ :=
  descSubgroupComponentGroupHom_unique H (centralizerHopfIdeal H x) φ hφ ψ hψ

/-- The kernel of the descended homomorphism on `A_G(x)` is the image of `ker φ` under
`centralizerComponentMap`. -/
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
      φ.ker.map (centralizerComponentMap H x) :=
  ker_descSubgroupComponentGroupHom H (centralizerHopfIdeal H x) φ hφ

/-- Descend a `C_G(x)(k)`-action on `X` whose restriction to `C_G(x)°(k)` is trivial to a
permutation representation of `A_G(x)`. -/
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
    centralizerComponentGroup H x →* Equiv.Perm X :=
  subgroupComponentGroupActionHom H (centralizerHopfIdeal H x) X htriv

/-- The descended `A_G(x)`-action agrees with the `C_G(x)(k)`-action. -/
@[simp]
theorem centralizerComponentGroupActionHom_centralizerComponentMap
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
    centralizerComponentGroupActionHom H x X htriv (centralizerComponentMap H x g) y = g • y :=
  subgroupComponentGroupActionHom_subgroupComponentMap H (centralizerHopfIdeal H x) X htriv g y

/-- The descended `MulAction` of `A_G(x)` on `X` from a `C_G(x)(k)`-action trivial on
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
    MulAction (centralizerComponentGroup H x) X :=
  MulAction.compHom X (centralizerComponentGroupActionHom H x X htriv)

/-- The orbits of the descended `A_G(x)`-action coincide with the `C_G(x)(k)`-orbits. -/
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
    MulAction.orbit (centralizerComponentGroup H x) y =
      MulAction.orbit (CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
        (CommAlgCat.of k k)) y :=
  orbit_subgroupComponentGroupMulAction H (centralizerHopfIdeal H x) X htriv y

/-- The stabilizer in `A_G(x)` of a point is the image of its `C_G(x)(k)`-stabilizer. -/
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
    MulAction.stabilizer (centralizerComponentGroup H x) y =
      (MulAction.stabilizer
        (CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
          (CommAlgCat.of k k)) y).map (centralizerComponentMap H x) :=
  stabilizer_subgroupComponentGroupMulAction H (centralizerHopfIdeal H x) X htriv y

/-- The fixed points of the descended `A_G(x)`-action coincide with the `C_G(x)(k)`-fixed points. -/
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
    MulAction.fixedPoints (centralizerComponentGroup H x) X =
      MulAction.fixedPoints
        (CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
          (CommAlgCat.of k k)) X :=
  fixedPoints_subgroupComponentGroupMulAction H (centralizerHopfIdeal H x) X htriv

end ActionDescent

/-- Transport a centralizer component group across an equality of Lie algebra elements. -/
noncomputable def centralizerComponentGroupEquivOfEq (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    {x y : Module.Dual k (Bialgebra.CotangentSpace k H)} (hxy : x = y) :
    centralizerComponentGroup H x ≃* centralizerComponentGroup H y := by
  subst hxy
  exact MulEquiv.refl _

/-- Transporting a rational-point component class along an equality of Lie algebra elements
preserves the underlying rational point. -/
@[simp]
theorem centralizerComponentGroupEquivOfEq_centralizerComponentMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    {x y : Module.Dual k (Bialgebra.CotangentSpace k H)} (hxy : x = y)
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) :
    centralizerComponentGroupEquivOfEq H hxy (centralizerComponentMap H x g) =
      centralizerComponentMap H y ⟨g.1, hxy ▸ g.2⟩ := by
  subst hxy
  rfl

/-- The centralizer component group of `0` is canonically isomorphic to `π₀(G)`. -/
noncomputable def centralizerComponentGroupZeroEquiv (H : FiniteTypeCommHopfAlgCat.{u, u} k) :
    centralizerComponentGroup H (0 : Module.Dual k (Bialgebra.CotangentSpace k H)) ≃*
      ConnectedComponents (PrimeSpectrum H) :=
  let e : H ≅ quotient H (centralizerHopfIdeal H 0) :=
    (quotientBotIso H).symm ≪≫
      eqToIso (congrArg (quotient H) (centralizerHopfIdeal_zero (k := k) (H := H)).symm)
  { toFun := mapComponentGroup e.hom
    invFun := mapComponentGroup e.inv
    left_inv C := by
      have h : (mapComponentGroup e.inv).comp (mapComponentGroup e.hom) = MonoidHom.id _ := by
        rw [← mapComponentGroup_comp, e.inv_hom_id, mapComponentGroup_id]
      exact DFunLike.congr_fun h C
    right_inv C := by
      have h : (mapComponentGroup e.hom).comp (mapComponentGroup e.inv) = MonoidHom.id _ := by
        rw [← mapComponentGroup_comp, e.hom_inv_id, mapComponentGroup_id]
      exact DFunLike.congr_fun h C
    map_mul' := (mapComponentGroup e.hom).map_mul }

/-- If `G` is connected, the inclusion `A_G(x) → π₀(G)` is trivial (even though `A_G(x)` itself may
be nontrivial). -/
theorem mapComponentGroup_mkQuotient_centralizer_eq_one (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    [ConnectedSpace (PrimeSpectrum H)]
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (C : centralizerComponentGroup H x) :
    mapComponentGroup (mkQuotient H (centralizerHopfIdeal H x)) C = 1 :=
  Subsingleton.elim _ _

section Conjugation

attribute [local instance] Derivation.adjointComodule

/-- Conjugation by `g ∈ G(k)` induces a canonical group isomorphism
`A_G(x) ≃* A_G(Ad(g) x)`. -/
noncomputable def centralizerComponentGroupConjugationEquiv
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k)) :
    centralizerComponentGroup H x ≃*
      centralizerComponentGroup H (Comodule.basePointsRepresentation (H := H) _ g x) :=
  componentGroupConjugationEquiv H (centralizerHopfIdeal H x)
    (centralizerHopfIdeal H (Comodule.basePointsRepresentation (H := H) _ g x)) g
    (centralizerHopfIdeal_basePointsRepresentation x g)

/-- On rational-point classes, `centralizerComponentGroupConjugationEquiv` sends `[h]` to
`[g h g⁻¹]`. -/
@[simp]
theorem centralizerComponentGroupConjugationEquiv_centralizerComponentMap
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (g : HopfAlgebra.points (R := k) (H := H) (CommAlgCat.of k k))
    (h : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k)) :
    centralizerComponentGroupConjugationEquiv H x g (centralizerComponentMap H x h) =
      centralizerComponentMap H (Comodule.basePointsRepresentation (H := H) _ g x)
        ⟨g * h.1 * g⁻¹,
          conj_mem_quotientPointsSubgroup_of_eq_conjugate H (centralizerHopfIdeal H x) _ g
            (centralizerHopfIdeal_basePointsRepresentation x g) h.2⟩ :=
  componentGroupConjugationEquiv_subgroupComponentMap H (centralizerHopfIdeal H x) _ g
    (centralizerHopfIdeal_basePointsRepresentation x g) h

/-- Self-conjugation by a rational point `g ∈ C_G(x)(k)` fixing `x` acts on `A_G(x)` by inner
conjugation by `[g] ∈ A_G(x)`. -/
theorem centralizerComponentGroupConjugationEquiv_self_eq_conj
    (H : FiniteTypeCommHopfAlgCat.{u, u} k)
    (x : Module.Dual k (Bialgebra.CotangentSpace k H))
    (g : CommHopfAlgCat.quotientPointsSubgroup H.obj (centralizerHopfIdeal H x)
      (CommAlgCat.of k k))
    (hx : Comodule.basePointsRepresentation (H := H) _ g.1 x = x) :
    (centralizerComponentGroupConjugationEquiv H x g.1).trans
        (centralizerComponentGroupEquivOfEq H hx) =
      MulAut.conj (centralizerComponentMap H x g) := by
  ext C
  obtain ⟨h, rfl⟩ := centralizerComponentMap_surjective H x C
  rw [MulEquiv.trans_apply, centralizerComponentGroupConjugationEquiv_centralizerComponentMap,
    centralizerComponentGroupEquivOfEq_centralizerComponentMap, MulAut.conj_apply,
    ← map_inv, ← map_mul, ← map_mul]
  rfl

end Conjugation

section FunctorAndIsogeny

/-- A morphism `f : H ⟶ K` of finite-type commutative Hopf algebras (representing `Spec K → Spec H`)
induces a canonical homomorphism `A_K(x) →* A_H(df(x))` on centralizer component groups. -/
noncomputable def mapCentralizerComponentGroup {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    centralizerComponentGroup K x →*
      centralizerComponentGroup H (dualCotangentMap f.hom.hom x) :=
  mapComponentGroup
    (ofHom (f.hom.hom.centralizerMap x) :
      quotient H (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x)) ⟶
        quotient K (centralizerHopfIdeal K x))

omit [IsAlgClosed k] in
/-- A morphism of affine groups maps `A`-points of `C_K(x)` into `A`-points of `C_H(df(x))`. -/
theorem mapDomain_mem_centralizer_dualCotangentMap {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (A : CommAlgCat.{u} k)
    {g : HopfAlgebra.points (R := k) (H := K) A}
    (hg : g ∈ CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x) A) :
    BialgHom.mapDomain (A := A) f.hom.hom g ∈
      CommHopfAlgCat.quotientPointsSubgroup H.obj
        (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x)) A := by
  have hmem := (CommHopfAlgCat.mem_quotientPointsSubgroup_map_iff f.hom
    (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x)) A g).mp
    (CommHopfAlgCat.quotientPointsSubgroup_le_of_le K.obj
      (f.hom.hom.map_centralizerHopfIdeal_le x) _ hg)
  simpa only [CommHopfAlgCat.Hom.mapPointsFunctor_app_apply, ← BialgHom.mapDomain_apply] using hmem

/-- On rational-point classes, `mapCentralizerComponentGroup` applies `mapDomain f` to the
representing rational point. -/
@[simp]
theorem mapCentralizerComponentGroup_centralizerComponentMap
    {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (g : CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x)
      (CommAlgCat.of k k)) :
    mapCentralizerComponentGroup f x (centralizerComponentMap K x g) =
      centralizerComponentMap H (dualCotangentMap f.hom.hom x)
        ⟨BialgHom.mapDomain (A := k) f.hom.hom g.1,
          mapDomain_mem_centralizer_dualCotangentMap f x (CommAlgCat.of k k) g.2⟩ := by
  obtain ⟨q, rfl⟩ := (CommHopfAlgCat.quotientPointsSubgroupIso K.obj (centralizerHopfIdeal K x)
    (CommAlgCat.of k k)).groupIsoToMulEquiv.surjective g
  have hqeq :
      (CommHopfAlgCat.quotientPointsSubgroupIso K.obj (centralizerHopfIdeal K x)
        (CommAlgCat.of k k)).groupIsoToMulEquiv q =
      ⟨CommHopfAlgCat.quotientPointsHom K.obj (centralizerHopfIdeal K x) (CommAlgCat.of k k) q,
        CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup K.obj _ _ q⟩ :=
    CommHopfAlgCat.quotientPointsSubgroupIso_hom_apply K.obj (centralizerHopfIdeal K x)
      (CommAlgCat.of k k) q
  rw [hqeq, centralizerComponentMap_quotientPointsHom]
  have hmap : mapCentralizerComponentGroup f x
      ((quotient K (centralizerHopfIdeal K x)).rationalComponentMap q) =
      (quotient H (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x))).rationalComponentMap
        (BialgHom.mapDomain (A := k) (f.hom.hom.centralizerMap x) q) :=
    mapComponentGroup_rationalComponentMap
      (ofHom (f.hom.hom.centralizerMap x) :
        quotient H (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x)) ⟶
          quotient K (centralizerHopfIdeal K x)) q
  rw [hmap]
  let q' : HopfAlgebra.points (R := k)
      (H := quotient H (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x)))
      (CommAlgCat.of k k) :=
    BialgHom.mapDomain (A := k) (f.hom.hom.centralizerMap x) q
  have hval :
      CommHopfAlgCat.quotientPointsHom H.obj
          (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x)) (CommAlgCat.of k k) q' =
        BialgHom.mapDomain (A := k) f.hom.hom
          (CommHopfAlgCat.quotientPointsHom K.obj (centralizerHopfIdeal K x)
            (CommAlgCat.of k k) q) := by
    apply WithConv.ofConv_injective
    ext a
    rw [CommHopfAlgCat.quotientPointsHom_apply_apply, Ideal.Quotient.mkₐ_eq_mk]
    dsimp only [q']
    rw [BialgHom.mapDomain_apply_apply, BialgHom.mapDomain_apply_apply,
      BialgHom.centralizerMap_mk, CommHopfAlgCat.quotientPointsHom_apply_apply,
      Ideal.Quotient.mkₐ_eq_mk]
  have hsub :
      (⟨BialgHom.mapDomain (A := k) f.hom.hom
          (CommHopfAlgCat.quotientPointsHom K.obj (centralizerHopfIdeal K x) (CommAlgCat.of k k) q),
        mapDomain_mem_centralizer_dualCotangentMap f x (CommAlgCat.of k k)
          (CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup K.obj _ _ q)⟩ :
        CommHopfAlgCat.quotientPointsSubgroup H.obj
          (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x)) (CommAlgCat.of k k)) =
      ⟨CommHopfAlgCat.quotientPointsHom H.obj
          (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x)) (CommAlgCat.of k k) q',
        CommHopfAlgCat.quotientPointsHom_mem_quotientPointsSubgroup H.obj _ _ q'⟩ :=
    Subtype.ext hval.symm
  rw [hsub, centralizerComponentMap_quotientPointsHom]

/-- `mapCentralizerComponentGroup` commutes with the inclusions `A_K(x) → π₀(K)` and
`A_H(df(x)) → π₀(H)` into the ambient component groups. -/
theorem mapComponentGroup_mkQuotient_mapCentralizerComponentGroup
    {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (C : centralizerComponentGroup K x) :
    mapComponentGroup (mkQuotient H (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x)))
        (mapCentralizerComponentGroup f x C) =
      mapComponentGroup f (mapComponentGroup (mkQuotient K (centralizerHopfIdeal K x)) C) := by
  obtain ⟨g, rfl⟩ := centralizerComponentMap_surjective K x C
  rw [mapCentralizerComponentGroup_centralizerComponentMap]
  -- `centralizerComponentMap` is definitionally `subgroupComponentMap`.
  change mapComponentGroup (mkQuotient H _) (subgroupComponentMap H _ _) =
    mapComponentGroup f (mapComponentGroup (mkQuotient K _) (subgroupComponentMap K _ g))
  rw [mapComponentGroup_mkQuotient_subgroupComponentMap,
    mapComponentGroup_mkQuotient_subgroupComponentMap,
    mapComponentGroup_rationalComponentMap]

section ConjugationNaturality

attribute [local instance] Derivation.adjointComodule

/-- `mapCentralizerComponentGroup` commutes with conjugation by a rational point `g ∈ K(k)`. -/
theorem mapCentralizerComponentGroup_conjugationEquiv
    {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (x : Module.Dual k (Bialgebra.CotangentSpace k K))
    (g : HopfAlgebra.points (R := k) (H := K) (CommAlgCat.of k k))
    (hxy : dualCotangentMap f.hom.hom (Comodule.basePointsRepresentation (H := K) _ g x) =
      Comodule.basePointsRepresentation (H := H) _ (BialgHom.mapDomain (A := k) f.hom.hom g)
        (dualCotangentMap f.hom.hom x))
    (C : centralizerComponentGroup K x) :
    centralizerComponentGroupEquivOfEq H hxy
        (mapCentralizerComponentGroup f (Comodule.basePointsRepresentation (H := K) _ g x)
          (centralizerComponentGroupConjugationEquiv K x g C)) =
      centralizerComponentGroupConjugationEquiv H (dualCotangentMap f.hom.hom x)
        (BialgHom.mapDomain (A := k) f.hom.hom g)
        (mapCentralizerComponentGroup f x C) := by
  obtain ⟨h, rfl⟩ := centralizerComponentMap_surjective K x C
  let hconj : CommHopfAlgCat.quotientPointsSubgroup K.obj
      (centralizerHopfIdeal K (Comodule.basePointsRepresentation (H := K) _ g x))
      (CommAlgCat.of k k) :=
    ⟨g * h.1 * g⁻¹,
      conj_mem_quotientPointsSubgroup_of_eq_conjugate K (centralizerHopfIdeal K x) _ g
        (centralizerHopfIdeal_basePointsRepresentation x g) h.2⟩
  let himg : CommHopfAlgCat.quotientPointsSubgroup H.obj
      (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x)) (CommAlgCat.of k k) :=
    ⟨BialgHom.mapDomain (A := k) f.hom.hom h.1,
      mapDomain_mem_centralizer_dualCotangentMap f x (CommAlgCat.of k k) h.2⟩
  have hL1 : centralizerComponentGroupConjugationEquiv K x g (centralizerComponentMap K x h) =
      centralizerComponentMap K _ hconj :=
    centralizerComponentGroupConjugationEquiv_centralizerComponentMap K x g h
  have hL2 : mapCentralizerComponentGroup f (Comodule.basePointsRepresentation (H := K) _ g x)
      (centralizerComponentMap K _ hconj) =
      centralizerComponentMap H _
        ⟨BialgHom.mapDomain (A := k) f.hom.hom hconj.1,
          mapDomain_mem_centralizer_dualCotangentMap f _ (CommAlgCat.of k k) hconj.2⟩ :=
    mapCentralizerComponentGroup_centralizerComponentMap f _ hconj
  have hL3 := centralizerComponentGroupEquivOfEq_centralizerComponentMap H hxy
    ⟨BialgHom.mapDomain (A := k) f.hom.hom hconj.1,
      mapDomain_mem_centralizer_dualCotangentMap f _ (CommAlgCat.of k k) hconj.2⟩
  have hR1 : mapCentralizerComponentGroup f x (centralizerComponentMap K x h) =
      centralizerComponentMap H _ himg :=
    mapCentralizerComponentGroup_centralizerComponentMap f x h
  have hR2 := centralizerComponentGroupConjugationEquiv_centralizerComponentMap H
    (dualCotangentMap f.hom.hom x) (BialgHom.mapDomain (A := k) f.hom.hom g) himg
  refine (congrArg (fun z ↦ centralizerComponentGroupEquivOfEq H hxy
      (mapCentralizerComponentGroup f _ z)) hL1).trans ?_
  refine (congrArg (centralizerComponentGroupEquivOfEq H hxy) hL2).trans ?_
  refine hL3.trans ?_
  refine Eq.trans ?_ (congrArg (centralizerComponentGroupConjugationEquiv H _ _) hR1).symm
  refine Eq.trans ?_ hR2.symm
  exact congrArg (centralizerComponentMap H _)
    (Subtype.ext (by dsimp only [hconj, himg]; rw [map_mul, map_mul, map_inv]))

end ConjugationNaturality

/-- An isogeny with injective differential induces a surjection `A_K(x) ↠ A_H(df(x))`. -/
theorem mapCentralizerComponentGroup_surjective_of_injective_differential
    {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hinj : Function.Injective (dualCotangentMap f.hom.hom))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Surjective (mapCentralizerComponentGroup f x) :=
  mapComponentGroup_surjective_of_injective
    (ofHom (f.hom.hom.centralizerMap x) :
      quotient H (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x)) ⟶
        quotient K (centralizerHopfIdeal K x))
    (hf.centralizerMap_of_injective hinj x).faithfullyFlat.injective

/-- An isogeny with étale kernel induces a surjection `A_K(x) ↠ A_H(df(x))`. -/
theorem mapCentralizerComponentGroup_surjective_of_etaleKernel
    {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hker : Algebra.Etale k (K ⧸ (CommHopfAlgCat.kernelHopfIdeal f.hom).toIdeal))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Surjective (mapCentralizerComponentGroup f x) :=
  mapCentralizerComponentGroup_surjective_of_injective_differential f hf
    (hf.dualCotangentMap_bijective_of_etaleKernel hker).injective x

/-- In characteristic zero, every isogeny induces a surjection `A_K(x) ↠ A_H(df(x))`. -/
theorem mapCentralizerComponentGroup_surjective_of_charZero [CharZero k]
    {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Surjective (mapCentralizerComponentGroup f x) :=
  mapComponentGroup_surjective_of_injective
    (ofHom (f.hom.hom.centralizerMap x) :
      quotient H (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x)) ⟶
        quotient K (centralizerHopfIdeal K x))
    (hf.centralizerMap_of_charZero x).faithfullyFlat.injective

/-- For an isogeny `f` with injective differential, the sequence
`π₀(ker f ∩ C_K(x)) → A_K(x) → A_H(df(x))` is exact. -/
theorem mulExact_mapCentralizerComponentGroup_of_injective_differential
    {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hinj : Function.Injective (dualCotangentMap f.hom.hom))
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    let c : quotient H (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x)) ⟶
        quotient K (centralizerHopfIdeal K x) :=
      ofHom (f.hom.hom.centralizerMap x)
    Function.MulExact
      (mapComponentGroup (mkQuotient (quotient K (centralizerHopfIdeal K x))
        (CommHopfAlgCat.kernelHopfIdeal c.hom)))
      (mapCentralizerComponentGroup f x) :=
  mulExact_mapComponentGroup_kernel
    (ofHom (f.hom.hom.centralizerMap x) :
      quotient H (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x)) ⟶
        quotient K (centralizerHopfIdeal K x))
    (hf.centralizerMap_of_injective hinj x).faithfullyFlat

/-- **Central-isogeny exact sequence on centralizer component groups.**
For an isogeny `f` with injective differential and central kernel, the natural sequence
`π₀(ker f) → A_K(x) → A_H(df(x)) → 1` is exact at `A_K(x)` (and surjective at `A_H(df(x))` by
`mapCentralizerComponentGroup_surjective_of_injective_differential`). -/
theorem mulExact_mapCentralizerComponentGroup_of_isCentral
    {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hinj : Function.Injective (dualCotangentMap f.hom.hom))
    (hcent : (CommHopfAlgCat.kernelHopfIdeal f.hom).IsCentral)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K (centralizerHopfIdeal_le_of_isCentral hcent x)))
      (mapCentralizerComponentGroup f x) := by
  let c : quotient H (centralizerHopfIdeal H (dualCotangentMap f.hom.hom x)) ⟶
      quotient K (centralizerHopfIdeal K x) :=
    ofHom (f.hom.hom.centralizerMap x)
  have hex := mulExact_mapCentralizerComponentGroup_of_injective_differential f hf hinj x
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
theorem mulExact_mapCentralizerComponentGroup_of_isCentralIsogeny_of_charZero [CharZero k]
    {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (hf : CommHopfAlgCat.IsCentralIsogeny f.hom)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K
        (centralizerHopfIdeal_le_of_isCentral hf.isCentral_kernelHopfIdeal x)))
      (mapCentralizerComponentGroup f x) := by
  let Q := CommHopfAlgCat.quotient K.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)
  have het : Algebra.Etale k Q :=
    algebraEtale_iff_finite_and_isReduced.2
      ⟨CommHopfAlgCat.moduleFinite_quotient_kernelHopfIdeal hf.isIsogeny.finite,
        HopfAlgebra.isReduced_of_charZero k Q⟩
  exact mulExact_mapCentralizerComponentGroup_of_isCentral f hf.isIsogeny
    (hf.isIsogeny.dualCotangentMap_bijective_of_etaleKernel het).injective
    hf.isCentral_kernelHopfIdeal x

/-- In characteristic zero, every isogeny from a geometrically connected affine group is central
and therefore induces the exact sequence `π₀(ker f) → A_K(x) → A_H(df(x)) → 1`. -/
theorem mulExact_mapCentralizerComponentGroup_of_isIsogeny_of_connected_of_charZero [CharZero k]
    {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hK : geometricallyConnectedCommHopfAlgProperty k K.obj)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.MulExact
      (mapComponentGroup (quotientMapOfLe K
        (centralizerHopfIdeal_le_of_isCentral
          (hf.isCentralIsogeny_of_charZero hK).isCentral_kernelHopfIdeal x)))
      (mapCentralizerComponentGroup f x) :=
  mulExact_mapCentralizerComponentGroup_of_isCentralIsogeny_of_charZero f
    (hf.isCentralIsogeny_of_charZero hK) x

/-- For a central isogeny with injective differential, `A_K(x) → A_H(df(x))` is injective (hence
an isomorphism) if and only if every rational point of `ker f` lies in `C_K(x)°(k)`. -/
theorem injective_mapCentralizerComponentGroup_iff_of_isCentral
    {H K : FiniteTypeCommHopfAlgCat.{u, u} k}
    (f : H ⟶ K) (hf : CommHopfAlgCat.IsIsogeny f.hom)
    (hinj : Function.Injective (dualCotangentMap f.hom.hom))
    (hcent : (CommHopfAlgCat.kernelHopfIdeal f.hom).IsCentral)
    (x : Module.Dual k (Bialgebra.CotangentSpace k K)) :
    Function.Injective (mapCentralizerComponentGroup f x) ↔
      CommHopfAlgCat.quotientPointsSubgroup K.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)
          (CommAlgCat.of k k) ≤
        CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x).identityComponent
          (CommAlgCat.of k k) := by
  have hex := mulExact_mapCentralizerComponentGroup_of_isCentral f hf hinj hcent x
  rw [injective_iff_map_eq_one]
  constructor
  · intro hinjC g hg
    let gK : CommHopfAlgCat.quotientPointsSubgroup K.obj (CommHopfAlgCat.kernelHopfIdeal f.hom)
        (CommAlgCat.of k k) := ⟨g, hg⟩
    let gC : CommHopfAlgCat.quotientPointsSubgroup K.obj (centralizerHopfIdeal K x)
        (CommAlgCat.of k k) :=
      ⟨g, CommHopfAlgCat.quotientPointsSubgroup_le_of_le K.obj
        (centralizerHopfIdeal_le_of_isCentral hcent x) _ hg⟩
    have hmap : mapCentralizerComponentGroup f x
        (subgroupComponentMap K (centralizerHopfIdeal K x) gC) = 1 := by
      rw [← mapComponentGroup_quotientMapOfLe_subgroupComponentMap K
        (centralizerHopfIdeal_le_of_isCentral hcent x) gK]
      exact (hex _).mpr ⟨subgroupComponentMap K (CommHopfAlgCat.kernelHopfIdeal f.hom) gK, rfl⟩
    exact (subgroupComponentMap_eq_one_iff K (centralizerHopfIdeal K x) gC).mp (hinjC _ hmap)
  · intro hle C hC
    obtain ⟨D, rfl⟩ := (hex C).mp hC
    obtain ⟨gK, rfl⟩ := subgroupComponentMap_surjective K (CommHopfAlgCat.kernelHopfIdeal f.hom) D
    rw [mapComponentGroup_quotientMapOfLe_subgroupComponentMap]
    exact (subgroupComponentMap_eq_one_iff K (centralizerHopfIdeal K x) _).mpr (hle gK.2)

end FunctorAndIsogeny

end FiniteTypeCommHopfAlgCat

end TauCeti
