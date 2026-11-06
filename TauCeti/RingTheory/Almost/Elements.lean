/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Almost.Hom
public import Mathlib.CategoryTheory.Adjunction.Triple
import Mathlib.CategoryTheory.Adjunction.Additive
import Mathlib.CategoryTheory.Preadditive.LeftExact

/-!
# Almost elements and the left adjoint of almostification

Let `S = (V, m)` be a basic setup and `m~ = m ⊗[V] m`. The almostification functor
`M ↦ M^a` from `V`-modules to almost `V`-modules has a right adjoint and a left adjoint, both
fully faithful:

* the functor of *almost elements* `M ↦ M_* = Hom(V^a, M)`, the Hom-module out of the unit
  `V^a`; on almostifications it is `(N^a)_* ≅ Hom_V(m~, N)`;
* the functor `M ↦ M_!`, the firm module representing `M`; on almostifications it is
  `(N^a)_! ≅ m~ ⊗[V] N`, with counit the action map `m~ ⊗[V] N → N`.

The functor `(−)_!` is exact because `m~` is flat, and the unit `N → (N^a)_*`, the counit
`(N^a)_! → N` and the comparison `M_! → M_*` are almost isomorphisms. These adjoints are how
statements about almost modules are turned into statements about ordinary modules: `M_*` is the
module of almost elements of `M`, and `M_!` its canonical representative for tensor products and
colimits.

Both functors come from the firm-module model of almost modules
(`TauCeti.Almost.Module.firmEquiv`): `M_!` is the firm module representing `M`, and the right
adjoint is Bhatt's functor `j_* : N ↦ Hom_V(m~, N)` on firm modules. The adjunction for almost
elements is transported to the Hom-functor `Hom(V^a, −)` through the bijection
`Hom(V^a, M) ≅ Hom_V(V, M_*) = M_*`, and `(N^a)_* ≅ Hom_V(m~, N)` is the almost-Hom formula
`TauCeti.Almost.Module.homLinearEquiv` for `Hom(V^a, N^a)`.

## Main definitions

* `TauCeti.Almost.Module.elements`: the functor of almost elements `M ↦ M_* = Hom(V^a, M)`.
* `TauCeti.Almost.Module.shriek`: the functor `M ↦ M_!`.
* `TauCeti.Almost.Module.adjElements`: the adjunction `toAlmost S ⊣ elements S`.
* `TauCeti.Almost.Module.adjShriek`: the adjunction `shriek S ⊣ toAlmost S`.
* `TauCeti.Almost.Module.toAlmostCompElementsIso`: `(N^a)_* ≅ Hom_V(m~, N)`, naturally in `N`.
* `TauCeti.Almost.Module.toAlmostCompShriekIso`: `(N^a)_! ≅ m~ ⊗[V] N`, naturally in `N`.
* `TauCeti.Almost.Module.adjTriple`: the adjoint triple `shriek S ⊣ toAlmost S ⊣ elements S`.
* `TauCeti.Almost.Module.shriekToElements`: the natural map `M_! → M_*`.

## Main results

* `TauCeti.Almost.Module.adjElements_homEquiv_apply`: the adjunction sends `f : N^a → M` to
  `n ↦ (V → N, 1 ↦ n)^a ≫ f`.
* `TauCeti.Almost.Module.adjShriek_counit_app`: the counit `(N^a)_! → N` is the action map.
* `TauCeti.Almost.Module.fullyFaithfulElements` and `TauCeti.Almost.Module.fullyFaithfulShriek`:
  both adjoints are fully faithful, so the counit `(M_*)^a → M` and the unit `M → (M_!)^a` are
  isomorphisms (by Mathlib's instances for adjunctions with a fully faithful adjoint).
* `TauCeti.Almost.Module.isAlmostIso_adjElements_unit_app`: `N → (N^a)_*` is an almost
  isomorphism.
* `TauCeti.Almost.Module.isAlmostIso_adjShriek_counit_app`: `(N^a)_! → N` is an almost
  isomorphism.
* `TauCeti.Almost.Module.isAlmostIso_shriekToElements_app`: `M_! → M_*` is an almost
  isomorphism.
* The instance `PreservesFiniteLimits (shriek S)`: `(−)_!` is exact.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2,
  (2.2.9), Proposition 2.2.13 and Proposition 2.2.21.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.1, Construction 4.1.5 and
  Proposition 4.1.7.
* P. Scholze, *Perfectoid spaces*, Publ. Math. IHÉS 116 (2012), §4.
-/

public section

universe u

open CategoryTheory Limits Opposite

namespace TauCeti.Almost

variable {V : Type u} [CommRing V] (S : BasicSetup V)

namespace Module

/-! ### Almost elements -/

/-- The functor of **almost elements** `M ↦ M_* = Hom(V^a, M)` (Gabber–Ramero, §2.2): the
Hom-module out of the unit `V^a`, with the `V`-module structure of the Hom-types of almost
modules. It is right adjoint to almostification (`adjElements`). -/
@[expose] noncomputable def elements : Module S ⥤ ModuleCat.{u} V :=
  (linearCoyoneda V (Module S)).obj (op ((toAlmost S).obj (ModuleCat.of V V)))

@[simp]
theorem elements_obj (M : Module S) :
    (elements S).obj M = ModuleCat.of V ((toAlmost S).obj (ModuleCat.of V V) ⟶ M) :=
  (rfl)

@[simp]
theorem elements_map_hom_apply {M N : Module S} (f : M ⟶ N)
    (x : (toAlmost S).obj (ModuleCat.of V V) ⟶ M) :
    ((elements S).map f).hom x = x ≫ f :=
  (rfl)

instance : (elements S).Additive :=
  inferInstanceAs (Functor.Additive ((linearCoyoneda V (Module S)).obj _))

instance : (elements S).Linear V :=
  inferInstanceAs (Functor.Linear V ((linearCoyoneda V (Module S)).obj _))

/-- The firm model `M ↦ Hom_V(m~, M_!)` of almost elements. -/
private noncomputable abbrev elementsFirm : Module S ⥤ ModuleCat.{u} V :=
  (firmEquiv S).functor ⋙ S.closure

/-- Almostification is left adjoint to the firm model of almost elements. -/
private noncomputable def adjFirm : toAlmost S ⊣ elementsFirm S :=
  (S.firmAdj.comp (firmEquiv S).symm.toAdjunction).ofNatIsoLeft
    (Iso.isoCompInverse (toAlmostCompFirmIso S)).symm

/-- The adjunction `adjFirm` on Hom-modules is `V`-linear. -/
private noncomputable def adjFirmHomLinearEquiv (N : ModuleCat.{u} V) (M : Module S) :
    ((toAlmost S).obj N ⟶ M) ≃ₗ[V] (N ⟶ (elementsFirm S).obj M) where
  __ := (adjFirm S).homAddEquiv N M
  map_smul' r f := by
    change (adjFirm S).homEquiv N M (r • f) = r • (adjFirm S).homEquiv N M f
    simp only [Adjunction.homEquiv_unit, Functor.map_smul, Linear.comp_smul]

/-- The bijection `Hom(V^a, M) ≅ Hom_V(V, Hom_V(m~, M_!)) ≅ Hom_V(m~, M_!)`. -/
private noncomputable def elementsFirmLinearEquiv (M : Module S) :
    ((toAlmost S).obj (ModuleCat.of V V) ⟶ M) ≃ₗ[V] (elementsFirm S).obj M :=
  adjFirmHomLinearEquiv S _ M ≪≫ₗ ModuleCat.homLinearEquiv ≪≫ₗ
    LinearMap.ringLmapEquivSelf V V _

private theorem elementsFirmLinearEquiv_apply (M : Module S)
    (f : (toAlmost S).obj (ModuleCat.of V V) ⟶ M) :
    elementsFirmLinearEquiv S M f = ((adjFirm S).homEquiv _ _ f).hom 1 :=
  rfl

private theorem elementsFirmLinearEquiv_symm_apply (M : Module S) (x : (elementsFirm S).obj M) :
    (elementsFirmLinearEquiv S M).symm x = ((adjFirm S).homEquiv _ _).symm
      (ModuleCat.ofHom (LinearMap.toSpanSingleton V ((elementsFirm S).obj M) x)) :=
  rfl

/-- Almost elements agree with their firm model. -/
private noncomputable def elementsIsoFirm : elements S ≅ elementsFirm S :=
  NatIso.ofComponents (fun M ↦ (elementsFirmLinearEquiv S M).toModuleIso) fun {M N} f ↦ by
    ext x
    -- Both sides are `(adjFirm.homEquiv (x ≫ f)).hom 1`, by naturality of the adjunction.
    exact congrArg (fun g ↦ g.hom (1 : V)) ((adjFirm S).homEquiv_naturality_right x f)

private theorem elementsIsoFirm_inv_app_apply (M : Module S) (x : (elementsFirm S).obj M) :
    ((elementsIsoFirm S).inv.app M).hom x = (elementsFirmLinearEquiv S M).symm x :=
  rfl

/-- **Almostification is left adjoint to almost elements**: `Hom(N^a, M) ≅ Hom_V(N, M_*)`
(Gabber–Ramero, Proposition 2.2.13). The bijection is `adjElements_homEquiv_apply`. -/
noncomputable def adjElements : toAlmost S ⊣ elements S :=
  (adjFirm S).ofNatIsoRight (elementsIsoFirm S).symm

/-- The adjunction `adjElements` sends `f : N^a → M` to the linear map `N → Hom(V^a, M)`,
`n ↦ (V → N, 1 ↦ n)^a ≫ f`. -/
theorem adjElements_homEquiv_apply (N : ModuleCat.{u} V) (M : Module S)
    (f : (toAlmost S).obj N ⟶ M) (n : N) :
    ((adjElements S).homEquiv N M f).hom n =
      (toAlmost S).map (ModuleCat.ofHom (LinearMap.toSpanSingleton V N n)) ≫ f := by
  rw [adjElements, Adjunction.homEquiv_ofNatIsoRight_apply, Iso.symm_hom, ModuleCat.hom_comp,
    LinearMap.comp_apply, elementsIsoFirm_inv_app_apply, elementsFirmLinearEquiv_symm_apply]
  have h : ModuleCat.ofHom (LinearMap.toSpanSingleton V ((elementsFirm S).obj M)
      (((adjFirm S).homEquiv N M f).hom n)) =
      ModuleCat.ofHom (LinearMap.toSpanSingleton V N n) ≫ (adjFirm S).homEquiv N M f := by
    ext
    simp
  refine (congrArg ((adjFirm S).homEquiv _ M).symm h).trans ?_
  rw [Adjunction.homEquiv_naturality_left_symm, Equiv.symm_apply_apply]

/-- The unit `N → (N^a)_*` of `adjElements` sends `n` to the almostification of `1 ↦ n`. -/
theorem adjElements_unit_app_apply (N : ModuleCat.{u} V) (n : N) :
    ((adjElements S).unit.app N).hom n =
      (toAlmost S).map (ModuleCat.ofHom (LinearMap.toSpanSingleton V N n)) := by
  have h := adjElements_homEquiv_apply S N _ (𝟙 _) n
  rwa [Adjunction.homEquiv_id, Category.comp_id] at h

/-- The functor of almost elements is fully faithful (Gabber–Ramero, Proposition 2.2.13(ii)). -/
noncomputable def fullyFaithfulElements : (elements S).FullyFaithful :=
  ((firmEquiv S).fullyFaithfulFunctor.comp S.fullyFaithfulClosure).ofIso (elementsIsoFirm S).symm

instance : (elements S).Full :=
  (fullyFaithfulElements S).full

instance : (elements S).Faithful :=
  (fullyFaithfulElements S).faithful

/-- The almost-Hom formula for `Hom(V^a, N^a)`:
`Hom(V^a, N^a) ≅ Hom_V(m~ ⊗[V] V, N) ≅ Hom_V(m~, N)`. -/
private noncomputable def toAlmostElementsEquiv (N : ModuleCat.{u} V) :
    ((toAlmost S).obj (ModuleCat.of V V) ⟶ (toAlmost S).obj N) ≃ₗ[V]
      (ModuleCat.of V S.tilde ⟶ N) :=
  homLinearEquiv S (ModuleCat.of V V) N ≪≫ₗ
    LinearEquiv.arrowCongr (TensorProduct.rid V S.tilde) (LinearEquiv.refl V N) ≪≫ₗ
    (ModuleCat.homLinearEquiv (M := ModuleCat.of V S.tilde) (N := N) (S := V)).symm

private theorem toAlmostElementsEquiv_apply (N : ModuleCat.{u} V)
    (f : (toAlmost S).obj (ModuleCat.of V V) ⟶ (toAlmost S).obj N) :
    toAlmostElementsEquiv S N f = ModuleCat.ofHom
      (homLinearEquiv S _ N f ∘ₗ (TensorProduct.rid V S.tilde).symm.toLinearMap) :=
  rfl

/-- **The almost elements of an almostification**: `(N^a)_* ≅ Hom_V(m~, N)`, naturally in `N`
(Gabber–Ramero, Proposition 2.2.13(iii)). It is given by the almost-Hom formula `homLinearEquiv`
(`toAlmostCompElementsIso_hom_app_apply`). -/
noncomputable def toAlmostCompElementsIso :
    toAlmost S ⋙ elements S ≅ ihom (ModuleCat.of V S.tilde) :=
  NatIso.ofComponents (fun N ↦ (toAlmostElementsEquiv S N).toModuleIso) fun {N N'} g ↦ by
    refine ModuleCat.hom_ext (LinearMap.ext
      fun (f : (toAlmost S).obj (ModuleCat.of V V) ⟶ (toAlmost S).obj N) ↦ ?_)
    -- Both composites are evaluations of composed linear maps; this unfolds them.
    change toAlmostElementsEquiv S N' (f ≫ (toAlmost S).map g) = toAlmostElementsEquiv S N f ≫ g
    -- Postcomposition with `g^a` becomes postcomposition with `g` on representatives.
    have h := homLinearEquiv_natural S (𝟙 (ModuleCat.of V V)) g f
    rw [CategoryTheory.Functor.map_id, Category.id_comp] at h
    rw [toAlmostElementsEquiv_apply, toAlmostElementsEquiv_apply, h]
    ext t
    simp

/-- The isomorphism `(N^a)_* ≅ Hom_V(m~, N)` is the almost-Hom formula `homLinearEquiv` for
`Hom(V^a, N^a)`, composed with `m~ ≅ m~ ⊗[V] V`. -/
theorem toAlmostCompElementsIso_hom_app_apply (N : ModuleCat.{u} V)
    (f : (toAlmost S).obj (ModuleCat.of V V) ⟶ (toAlmost S).obj N) :
    ((toAlmostCompElementsIso S).hom.app N).hom f = ModuleCat.ofHom
      (homLinearEquiv S _ N f ∘ₗ (TensorProduct.rid V S.tilde).symm.toLinearMap) :=
  toAlmostElementsEquiv_apply S N f

/-- The unit `N → (N^a)_*` is an almost isomorphism (Gabber–Ramero, (2.2.9)). -/
theorem isAlmostIso_adjElements_unit_app (N : ModuleCat.{u} V) :
    S.IsAlmostIso ((adjElements S).unit.app N).hom := by
  rw [← isIso_toAlmost_map_iff]
  have := NatIso.isIso_app_of_isIso
    (Functor.whiskerRight (adjElements S).unit (toAlmost S)) N
  simpa using this

/-! ### The left adjoint `M ↦ M_!` -/

/-- The functor `M ↦ M_!` (Gabber–Ramero, §2.2): the firm module representing an almost module.
It is left adjoint to almostification (`adjShriek`). -/
noncomputable def shriek : Module S ⥤ ModuleCat.{u} V :=
  (firmEquiv S).functor ⋙ S.isFirm.ι

/-- **`(−)_!` is left adjoint to almostification** (Gabber–Ramero, Proposition 2.2.21):
`Hom_V(M_!, N) ≅ Hom(M, N^a)`. -/
noncomputable def adjShriek : shriek S ⊣ toAlmost S :=
  ((firmEquiv S).toAdjunction.comp S.firmInclusionAdj).ofNatIsoRight
    (Iso.isoCompInverse (toAlmostCompFirmIso S)).symm

/-- The functor `(−)_!` is fully faithful (Gabber–Ramero, Proposition 2.2.21). -/
noncomputable def fullyFaithfulShriek : (shriek S).FullyFaithful :=
  (firmEquiv S).fullyFaithfulFunctor.comp S.isFirm.fullyFaithfulι

instance : (shriek S).Full :=
  (fullyFaithfulShriek S).full

instance : (shriek S).Faithful :=
  (fullyFaithfulShriek S).faithful

/-- **`(−)_!` is exact**, as the kernel of a map of firm modules is firm (Gabber–Ramero,
Proposition 2.2.21). It preserves all colimits, being a left adjoint. -/
instance : PreservesFiniteLimits (shriek S) :=
  have := S.isFirm.preservesKernels_ι
  have := S.isFirm.ι.preservesFiniteLimits_of_preservesKernels
  inferInstanceAs (PreservesFiniteLimits ((firmEquiv S).functor ⋙ S.isFirm.ι))

/-- **The left adjoint on an almostification**: `(N^a)_! ≅ m~ ⊗[V] N`, naturally in `N`. -/
noncomputable def toAlmostCompShriekIso :
    toAlmost S ⋙ shriek S ≅ MonoidalCategory.tensorLeft (ModuleCat.of V S.tilde) :=
  (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight (toAlmostCompFirmIso S) _ ≪≫
    S.isFirm.liftCompιIso _ _

/-- Under `(N^a)_! ≅ m~ ⊗[V] N`, the counit `(N^a)_! → N` of `adjShriek` is the action map
`m~ ⊗[V] N → N`, `(x ⊗ y) ⊗ n ↦ (x * y) • n`. -/
theorem adjShriek_counit_app (N : ModuleCat.{u} V) :
    (adjShriek S).counit.app N =
      (toAlmostCompShriekIso S).hom.app N ≫ ModuleCat.ofHom (S.tildeAct N) := by
  -- Unfold the counit of the transported composite adjunction and the comparison isomorphism.
  have h1 : (adjShriek S).counit.app N =
      (shriek S).map ((Iso.isoCompInverse (toAlmostCompFirmIso S)).hom.app N) ≫
        ((firmEquiv S).toAdjunction.comp S.firmInclusionAdj).counit.app N :=
    rfl
  have h2 : (toAlmostCompShriekIso S).hom.app N =
      S.isFirm.ι.map ((toAlmostCompFirmIso S).hom.app N) :=
    rfl
  have h3 : (firmEquiv S).functor.map ((Iso.isoCompInverse (toAlmostCompFirmIso S)).hom.app N) ≫
      (firmEquiv S).counit.app (S.firm.obj N) = (toAlmostCompFirmIso S).hom.app N := by
    simp [Iso.isoCompInverse_hom_app]
  rw [h1, h2, Adjunction.comp_counit_app]
  -- `shriek` is `(firmEquiv S).functor ⋙ S.isFirm.ι`, and the counit of the equivalence's
  -- adjunction is its counit.
  change S.isFirm.ι.map ((firmEquiv S).functor.map
      ((Iso.isoCompInverse (toAlmostCompFirmIso S)).hom.app N)) ≫
    S.isFirm.ι.map ((firmEquiv S).counit.app (S.firm.obj N)) ≫ S.firmInclusionAdj.counit.app N = _
  rw [← Category.assoc, ← Functor.map_comp, h3]
  congr 1
  exact ModuleCat.hom_ext (S.firmInclusionAdj_counit_app_hom N)

/-- The counit `(N^a)_! → N` is an almost isomorphism (Gabber–Ramero, (2.2.9)). -/
theorem isAlmostIso_adjShriek_counit_app (N : ModuleCat.{u} V) :
    S.IsAlmostIso ((adjShriek S).counit.app N).hom := by
  rw [← isIso_toAlmost_map_iff]
  infer_instance

/-! ### The comparison `M_! → M_*` -/

/-- The adjoint triple `(−)_! ⊣ (−)^a ⊣ (−)_*`. -/
noncomputable def adjTriple : Adjunction.Triple (shriek S) (toAlmost S) (elements S) :=
  ⟨adjShriek S, adjElements S⟩

/-- The natural map `M_! → M_*` (Gabber–Ramero, (2.2.9)): Mathlib's comparison
`Adjunction.Triple.leftToRight` for the adjoint triple `adjTriple`, whose outer functors are fully
faithful. It corresponds under `adjElements` to the inverse of the unit isomorphism
`M ≅ (M_!)^a` (`shriekToElements_app`). -/
noncomputable abbrev shriekToElements : shriek S ⟶ elements S :=
  (adjTriple S).leftToRight

/-- The component `M_! → M_*` is the image under `adjElements` of the inverse of the unit
isomorphism `M ≅ (M_!)^a` of `adjShriek`. -/
theorem shriekToElements_app (M : Module S) :
    (shriekToElements S).app M = (adjElements S).homEquiv _ _ (inv ((adjShriek S).unit.app M)) := by
  rw [Adjunction.Triple.leftToRight_app, Adjunction.homEquiv_unit, Functor.map_inv]
  rfl

/-- The map `M_! → M_*` sends `x` to `(V → M_!, 1 ↦ x)^a` followed by `(M_!)^a ≅ M`. -/
theorem shriekToElements_app_apply (M : Module S) (x : (shriek S).obj M) :
    ((shriekToElements S).app M).hom x =
      (toAlmost S).map (ModuleCat.ofHom (LinearMap.toSpanSingleton V _ x)) ≫
        inv ((adjShriek S).unit.app M) := by
  rw [shriekToElements_app]
  exact adjElements_homEquiv_apply S _ _ _ x

/-- The map `M_! → M_*` is an almost isomorphism (Gabber–Ramero, (2.2.9)). -/
theorem isAlmostIso_shriekToElements_app (M : Module S) :
    S.IsAlmostIso ((shriekToElements S).app M).hom := by
  rw [← isIso_toAlmost_map_iff, shriekToElements_app]
  have h := ((adjElements S).homEquiv _ _).symm_apply_apply (inv ((adjShriek S).unit.app M))
  rw [Adjunction.homEquiv_counit] at h
  have : IsIso ((toAlmost S).map ((adjElements S).homEquiv _ _ (inv ((adjShriek S).unit.app M))) ≫
      (adjElements S).counit.app ((𝟭 (Module S)).obj M)) := by
    rw [h]
    infer_instance
  exact IsIso.of_isIso_comp_right _ ((adjElements S).counit.app ((𝟭 (Module S)).obj M))

end Module

end TauCeti.Almost
