/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.RepresentationTheory.Rep.TensorShortExact

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import TauCeti.RepresentationTheory.Induction.TrivialSubgroup

/-!
# The dimension-shifting sequences

For a representation `A` of a group `G`, the embedding `A ⟶ Coind_⊥^G A` into the representation
coinduced from the trivial subgroup and the projection `Ind_⊥^G A ⟶ A` from the induced
representation give short exact sequences

`0 ⟶ A ⟶ Coind_⊥^G A ⟶ dimensionShiftUp A ⟶ 0` and
`0 ⟶ dimensionShiftDown A ⟶ Ind_⊥^G A ⟶ A ⟶ 0`,

which stay short exact after restriction along any monoid homomorphism `H →* G`. The middle terms
have vanishing positive-degree cohomology, respectively homology, and for a finite group vanishing
Tate cohomology in every degree, so the connecting homomorphisms of these sequences shift degrees.
This is the *dimension shifting* of Milne, *Class Field Theory*, II 1.13 and 1.28; this file
provides the sequences themselves.

The constructions follow `ClassFieldTheory/Cohomology/Functors/UpDown.lean` in
`kbuzzard/ClassFieldTheory`, commit `ccc3323c6750abca25b49b35106f54eb3a398509`.

## Main definitions

* `Rep.dimensionShiftUp`, `Rep.dimensionShiftUpπ`, `Rep.dimensionShiftUpSES`: the cokernel of
  `A ⟶ Coind_⊥^G A` and its short complex.
* `Rep.dimensionShiftDown`, `Rep.dimensionShiftDownι`, `Rep.dimensionShiftDownSES`: the kernel of
  `Ind_⊥^G A ⟶ A` and its short complex.
* `Rep.dimensionShiftUpπIsCokernel`, `Rep.dimensionShiftDownιIsKernel`: their universal
  properties. The definitions are opaque, so consumers construct maps through these properties.

## Main statements

* `Rep.dimensionShiftUpSES_def`, `Rep.dimensionShiftDownSES_def`: the maps in the two short
  complexes.
* `Rep.dimensionShiftUpSES_shortExact`, `Rep.dimensionShiftUpSES_res_shortExact`,
  `Rep.dimensionShiftUpSES_tensorLeft_shortExact`: the upward sequence is short exact, also after
  restriction and after tensoring on the left with any representation.
* `Rep.dimensionShiftDownSES_shortExact`, `Rep.dimensionShiftDownSES_res_shortExact`,
  `Rep.dimensionShiftDownSES_tensorLeft_shortExact`: the same for the downward sequence.
* `Rep.dimensionShiftUpMap`, `Rep.dimensionShiftDownMap`: coefficient maps on both shifts,
  characterized by commutation with the quotient projection and kernel inclusion.
* `Rep.coindBotUnit_naturality`, `Rep.indBotCounit_naturality`: naturality of the maps defining
  the two sequences.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, §1.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §7.
-/

public noncomputable section

universe u

open CategoryTheory Limits MonoidalCategory

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

/-! ### The upward dimension shift -/

/-- The cokernel of the embedding `A ⟶ Coind_⊥^G A`, so that
`Hⁿ⁺¹(G, dimensionShiftUp A) ≅ Hⁿ⁺²(G, A)`. -/
def dimensionShiftUp (A : Rep k G) : Rep k G := cokernel (coindBotUnit A)

/-- The projection from the coinduced module onto `dimensionShiftUp A`. -/
def dimensionShiftUpπ (A : Rep k G) : coindBot k G A.V ⟶ dimensionShiftUp A :=
  cokernel.π (coindBotUnit A)

/-- The projection onto `dimensionShiftUp A` is an epimorphism. -/
instance dimensionShiftUpπ_epi (A : Rep k G) : Epi (dimensionShiftUpπ A) :=
  inferInstanceAs (Epi (cokernel.π (coindBotUnit A)))

/-- The embedding into the coinduced module followed by the dimension-shift projection is zero. -/
@[reassoc (attr := simp)]
theorem coindBotUnit_comp_dimensionShiftUpπ (A : Rep k G) :
    coindBotUnit A ≫ dimensionShiftUpπ A = 0 :=
  cokernel.condition (coindBotUnit A)

/-- The dimension-shift projection is a cokernel of the embedding into the coinduced module. -/
def dimensionShiftUpπIsCokernel (A : Rep k G) :
    IsColimit (CokernelCofork.ofπ (dimensionShiftUpπ A)
      (coindBotUnit_comp_dimensionShiftUpπ A)) :=
  cokernelIsCokernel (coindBotUnit A)

/-- The short complex `A ⟶ Coind_⊥^G A ⟶ dimensionShiftUp A`. -/
def dimensionShiftUpSES (A : Rep k G) : ShortComplex (Rep k G) :=
  ShortComplex.cokernelSequence (coindBotUnit A)

/-- The upward dimension-shifting short complex has maps the embedding into the coinduced module
and the dimension-shift projection. -/
theorem dimensionShiftUpSES_def (A : Rep k G) :
    dimensionShiftUpSES A = ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
      (coindBotUnit_comp_dimensionShiftUpπ A) :=
  (rfl)

/-- The first object in the upward dimension-shifting short complex is `A`. -/
@[simp]
theorem dimensionShiftUpSES_X₁ (A : Rep k G) : (dimensionShiftUpSES A).X₁ = A :=
  (rfl)

/-- The middle object in the upward dimension-shifting short complex is coinduced from `⊥`. -/
@[simp]
theorem dimensionShiftUpSES_X₂ (A : Rep k G) :
    (dimensionShiftUpSES A).X₂ = coindBot k G A.V :=
  (rfl)

/-- The last object in the upward dimension-shifting short complex is `dimensionShiftUp A`. -/
@[simp]
theorem dimensionShiftUpSES_X₃ (A : Rep k G) :
    (dimensionShiftUpSES A).X₃ = dimensionShiftUp A :=
  (rfl)

/-- The short complex `A ⟶ Coind_⊥^G A ⟶ dimensionShiftUp A` is short exact. -/
theorem dimensionShiftUpSES_shortExact (A : Rep k G) : (dimensionShiftUpSES A).ShortExact :=
  TauCeti.cokernelSequence_shortExact (coindBotUnit A)

/-- The upward dimension-shifting short complex stays short exact after restriction along any
monoid homomorphism `f : H →* G`. -/
theorem dimensionShiftUpSES_res_shortExact (A : Rep k G) {H : Type*} [Monoid H] (f : H →* G) :
    ((dimensionShiftUpSES A).map (resFunctor f)).ShortExact :=
  (shortExact_res f).mpr (dimensionShiftUpSES_shortExact A)

/-- The upward dimension-shifting short complex stays short exact after tensoring on the left with
any representation `M`: the embedding into the coinduced module has the `k`-linear retraction
`f ↦ f 1`. -/
theorem dimensionShiftUpSES_tensorLeft_shortExact (A M : Rep k G) :
    ((dimensionShiftUpSES A).map (tensorLeft M)).ShortExact := by
  have : Epi (dimensionShiftUpSES A).g := (dimensionShiftUpSES_shortExact A).epi_g
  exact shortExact_map_tensorLeft_of_leftInverse (dimensionShiftUpSES_shortExact A).exact M _
    (leftInverse_coindBotUnit A)

/-! ### The downward dimension shift -/

/-- The kernel of the projection `Ind_⊥^G A ⟶ A`, so that
`Ĥⁿ(G, A) ≅ Ĥⁿ⁺¹(G, dimensionShiftDown A)` when `G` is finite. -/
def dimensionShiftDown (A : Rep k G) : Rep k G := kernel (indBotCounit A)

/-- The inclusion of `dimensionShiftDown A` into the induced module. -/
def dimensionShiftDownι (A : Rep k G) : dimensionShiftDown A ⟶ indBot k G A.V :=
  kernel.ι (indBotCounit A)

/-- The inclusion of `dimensionShiftDown A` is a monomorphism. -/
instance dimensionShiftDownι_mono (A : Rep k G) : Mono (dimensionShiftDownι A) :=
  inferInstanceAs (Mono (kernel.ι (indBotCounit A)))

/-- The dimension-shift inclusion followed by the projection onto `A` is zero. -/
@[reassoc (attr := simp)]
theorem dimensionShiftDownι_comp_indBotCounit (A : Rep k G) :
    dimensionShiftDownι A ≫ indBotCounit A = 0 :=
  kernel.condition (indBotCounit A)

/-- The dimension-shift inclusion is a kernel of the projection onto `A`. -/
def dimensionShiftDownιIsKernel (A : Rep k G) :
    IsLimit (KernelFork.ofι (dimensionShiftDownι A)
      (dimensionShiftDownι_comp_indBotCounit A)) :=
  kernelIsKernel (indBotCounit A)

/-- The short complex `dimensionShiftDown A ⟶ Ind_⊥^G A ⟶ A`. -/
def dimensionShiftDownSES (A : Rep k G) : ShortComplex (Rep k G) :=
  ShortComplex.kernelSequence (indBotCounit A)

/-- The downward dimension-shifting short complex has maps the dimension-shift inclusion and the
projection onto `A`. -/
theorem dimensionShiftDownSES_def (A : Rep k G) :
    dimensionShiftDownSES A = ShortComplex.mk (dimensionShiftDownι A) (indBotCounit A)
      (dimensionShiftDownι_comp_indBotCounit A) :=
  (rfl)

/-- The first object in the downward dimension-shifting short complex is `dimensionShiftDown A`. -/
@[simp]
theorem dimensionShiftDownSES_X₁ (A : Rep k G) :
    (dimensionShiftDownSES A).X₁ = dimensionShiftDown A :=
  (rfl)

/-- The middle object in the downward dimension-shifting short complex is induced from `⊥`. -/
@[simp]
theorem dimensionShiftDownSES_X₂ (A : Rep k G) :
    (dimensionShiftDownSES A).X₂ = indBot k G A.V :=
  (rfl)

/-- The last object in the downward dimension-shifting short complex is `A`. -/
@[simp]
theorem dimensionShiftDownSES_X₃ (A : Rep k G) : (dimensionShiftDownSES A).X₃ = A :=
  (rfl)

/-- The short complex `dimensionShiftDown A ⟶ Ind_⊥^G A ⟶ A` is short exact. -/
theorem dimensionShiftDownSES_shortExact (A : Rep k G) :
    (dimensionShiftDownSES A).ShortExact :=
  TauCeti.kernelSequence_shortExact (indBotCounit A)

/-- The downward dimension-shifting short complex stays short exact after restriction along any
monoid homomorphism `f : H →* G`. -/
theorem dimensionShiftDownSES_res_shortExact (A : Rep k G) {H : Type*} [Monoid H] (f : H →* G) :
    ((dimensionShiftDownSES A).map (resFunctor f)).ShortExact :=
  (shortExact_res f).mpr (dimensionShiftDownSES_shortExact A)

/-- The downward dimension-shifting short complex stays short exact after tensoring on the left
with any representation `M`: the projection from the induced module has the `k`-linear section
`a ↦ ⟦1 ⊗ₜ a⟧`. -/
theorem dimensionShiftDownSES_tensorLeft_shortExact (A M : Rep k G) :
    ((dimensionShiftDownSES A).map (tensorLeft M)).ShortExact := by
  have hs : Function.RightInverse (Representation.IndV.mk (⊥ : Subgroup G).subtype
      (Representation.trivial k (⊥ : Subgroup G) A.V) 1) (indBotCounit A).hom := fun a ↦ by
    rw [indBotCounit_hom_mk, inv_one, map_one, Module.End.one_apply]
  have : Mono (dimensionShiftDownSES A).f := (dimensionShiftDownSES_shortExact A).mono_f
  exact shortExact_map_tensorLeft_of_rightInverse (dimensionShiftDownSES_shortExact A).exact M _ hs

/-! ### Functoriality of the dimension-shifting sequences -/

/-- The morphism induced on the upward dimension shift by a representation morphism. -/
def dimensionShiftUpMap {A B : Rep k G} (f : A ⟶ B) :
    dimensionShiftUp A ⟶ dimensionShiftUp B :=
  cokernel.map (coindBotUnit A) (coindBotUnit B) f (coindBotMap f)
    (coindBotUnit_naturality f).symm

/-- The map on upward shifts commutes with their quotient projections. -/
@[reassoc (attr := simp)]
theorem dimensionShiftUpπ_naturality {A B : Rep k G} (f : A ⟶ B) :
    dimensionShiftUpπ A ≫ dimensionShiftUpMap f =
      coindBotMap f ≫ dimensionShiftUpπ B := by
  exact cokernel.π_desc _ _ _

/-- The upward shift map preserves identity morphisms. -/
@[simp]
theorem dimensionShiftUpMap_id (A : Rep k G) : dimensionShiftUpMap (𝟙 A) = 𝟙 _ := by
  simp [dimensionShiftUpMap, dimensionShiftUp]

/-- The upward shift map preserves composition. -/
@[simp]
theorem dimensionShiftUpMap_comp {A B C : Rep k G} (f : A ⟶ B) (g : B ⟶ C) :
    dimensionShiftUpMap (f ≫ g) = dimensionShiftUpMap f ≫ dimensionShiftUpMap g := by
  apply (cancel_epi (dimensionShiftUpπ A)).mp
  calc
    dimensionShiftUpπ A ≫ dimensionShiftUpMap (f ≫ g) =
        coindBotMap (f ≫ g) ≫ dimensionShiftUpπ C :=
      dimensionShiftUpπ_naturality (f ≫ g)
    _ = (coindBotMap f ≫ coindBotMap g) ≫ dimensionShiftUpπ C := by
      rw [coindBotMap_comp]
    _ = coindBotMap f ≫ (coindBotMap g ≫ dimensionShiftUpπ C) :=
      Category.assoc _ _ _
    _ = coindBotMap f ≫ (dimensionShiftUpπ B ≫ dimensionShiftUpMap g) := by
      rw [dimensionShiftUpπ_naturality g]
    _ = (coindBotMap f ≫ dimensionShiftUpπ B) ≫ dimensionShiftUpMap g :=
      (Category.assoc _ _ _).symm
    _ = (dimensionShiftUpπ A ≫ dimensionShiftUpMap f) ≫ dimensionShiftUpMap g := by
      rw [dimensionShiftUpπ_naturality f]

/-- A coefficient morphism induces a morphism of the public presentations of the upward
dimension-shifting sequences (`dimensionShiftUpSES_def`). -/
def dimensionShiftUpSESMap {A B : Rep k G} (f : A ⟶ B) :
    ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
        (coindBotUnit_comp_dimensionShiftUpπ A) ⟶
      ShortComplex.mk (coindBotUnit B) (dimensionShiftUpπ B)
        (coindBotUnit_comp_dimensionShiftUpπ B) :=
  { τ₁ := f
    τ₂ := coindBotMap f
    τ₃ := dimensionShiftUpMap f
    comm₁₂ := coindBotUnit_naturality f
    comm₂₃ := (dimensionShiftUpπ_naturality f).symm }

/-- The first component of the upward sequence morphism. -/
@[simp]
theorem dimensionShiftUpSESMap_τ₁ {A B : Rep k G} (f : A ⟶ B) :
    (dimensionShiftUpSESMap f).τ₁ = f := (rfl)

/-- The middle component of the upward sequence morphism. -/
@[simp]
theorem dimensionShiftUpSESMap_τ₂ {A B : Rep k G} (f : A ⟶ B) :
    (dimensionShiftUpSESMap f).τ₂ = coindBotMap f := (rfl)

/-- The last component of the upward sequence morphism. -/
@[simp]
theorem dimensionShiftUpSESMap_τ₃ {A B : Rep k G} (f : A ⟶ B) :
    (dimensionShiftUpSESMap f).τ₃ = dimensionShiftUpMap f := (rfl)

/-- The morphism induced on the downward dimension shift by a representation morphism. -/
def dimensionShiftDownMap {A B : Rep k G} (f : A ⟶ B) :
    dimensionShiftDown A ⟶ dimensionShiftDown B :=
  kernel.map (indBotCounit A) (indBotCounit B) (indBotMap f) f
    (indBotCounit_naturality f).symm

/-- The map on downward shifts commutes with their inclusions into induced modules. -/
@[reassoc (attr := simp)]
theorem dimensionShiftDownι_naturality {A B : Rep k G} (f : A ⟶ B) :
    dimensionShiftDownMap f ≫ dimensionShiftDownι B =
      dimensionShiftDownι A ≫ indBotMap f := by
  exact kernel.lift_ι _ _ _

/-- The downward shift map preserves identity morphisms. -/
@[simp]
theorem dimensionShiftDownMap_id (A : Rep k G) : dimensionShiftDownMap (𝟙 A) = 𝟙 _ := by
  simp only [dimensionShiftDownMap, dimensionShiftDown, indBotMap_id]
  -- Unfold the kernel wrapper to apply the generic identity law for `kernel.map`.
  change kernel.map (indBotCounit A) (indBotCounit A)
    (𝟙 (indBot k G A.V)) (𝟙 A) _ = 𝟙 _
  exact kernel.map_id (indBotCounit A) (𝟙 A) (by simp)

/-- The downward shift map preserves composition. -/
@[simp]
theorem dimensionShiftDownMap_comp {A B C : Rep k G} (f : A ⟶ B) (g : B ⟶ C) :
    dimensionShiftDownMap (f ≫ g) = dimensionShiftDownMap f ≫ dimensionShiftDownMap g := by
  apply (cancel_mono (dimensionShiftDownι C)).mp
  simp [dimensionShiftDownMap, dimensionShiftDownι, dimensionShiftDown, kernel.map, indBotMap_comp]

/-- A coefficient morphism induces a morphism of the public presentations of the downward
dimension-shifting sequences (`dimensionShiftDownSES_def`). -/
def dimensionShiftDownSESMap {A B : Rep k G} (f : A ⟶ B) :
    ShortComplex.mk (dimensionShiftDownι A) (indBotCounit A)
        (dimensionShiftDownι_comp_indBotCounit A) ⟶
      ShortComplex.mk (dimensionShiftDownι B) (indBotCounit B)
        (dimensionShiftDownι_comp_indBotCounit B) :=
  { τ₁ := dimensionShiftDownMap f
    τ₂ := indBotMap f
    τ₃ := f
    comm₁₂ := dimensionShiftDownι_naturality f
    comm₂₃ := indBotCounit_naturality f }

/-- The first component of the downward sequence morphism. -/
@[simp]
theorem dimensionShiftDownSESMap_τ₁ {A B : Rep k G} (f : A ⟶ B) :
    (dimensionShiftDownSESMap f).τ₁ = dimensionShiftDownMap f := (rfl)

/-- The middle component of the downward sequence morphism. -/
@[simp]
theorem dimensionShiftDownSESMap_τ₂ {A B : Rep k G} (f : A ⟶ B) :
    (dimensionShiftDownSESMap f).τ₂ = indBotMap f := (rfl)

/-- The last component of the downward sequence morphism. -/
@[simp]
theorem dimensionShiftDownSESMap_τ₃ {A B : Rep k G} (f : A ⟶ B) :
    (dimensionShiftDownSESMap f).τ₃ = f := (rfl)

variable {A B : Rep k G}

/-! ### Bundled coefficient functoriality -/

/-- The upward dimension shift as an endofunctor on representations. -/
@[expose] def dimensionShiftUpFunctor : Rep k G ⥤ Rep k G where
  obj := dimensionShiftUp
  map := fun f => dimensionShiftUpMap f
  map_id := dimensionShiftUpMap_id
  map_comp := fun f g => dimensionShiftUpMap_comp f g

/-- The upward shift functor evaluates to the upward shift. -/
@[simp] theorem dimensionShiftUpFunctor_obj (A : Rep k G) :
    (dimensionShiftUpFunctor (k := k) (G := G)).obj A = dimensionShiftUp A := rfl

/-- The upward shift functor acts on morphisms by `dimensionShiftUpMap`. -/
@[simp] theorem dimensionShiftUpFunctor_map (f : A ⟶ B) :
    (dimensionShiftUpFunctor (k := k) (G := G)).map f = dimensionShiftUpMap f := rfl

/-- The projection from coinduction to the upward shift, natural in coefficients. -/
@[expose] def dimensionShiftUpπNatTrans : coindBotRepFunctor (k := k) (G := G) ⟶
    dimensionShiftUpFunctor (k := k) (G := G) where
  app A := dimensionShiftUpπ A
  naturality := by
    intro A B f
    simpa only [coindBotRepFunctor_obj, dimensionShiftUpFunctor_obj,
      coindBotRepFunctor_map, dimensionShiftUpFunctor_map] using
      (dimensionShiftUpπ_naturality f).symm

/-- The component of the upward projection is the cokernel projection. -/
@[simp] theorem dimensionShiftUpπNatTrans_app (A : Rep k G) :
    (dimensionShiftUpπNatTrans (k := k) (G := G)).app A = dimensionShiftUpπ A := rfl

/-- The upward short exact sequence as a functor of coefficient representations. -/
@[expose] def dimensionShiftUpSESFunctor : Rep k G ⥤ ShortComplex (Rep k G) :=
  (ShortComplex.functorEquivalence (Rep k G) (Rep k G)).functor.obj
    (ShortComplex.mk (coindBotUnitNatTrans (k := k) (G := G))
      (dimensionShiftUpπNatTrans (k := k) (G := G)) (by
        apply NatTrans.ext
        funext A
        simp only [NatTrans.comp_app, zero_app, coindBotUnitNatTrans_app,
          dimensionShiftUpπNatTrans_app]
        exact coindBotUnit_comp_dimensionShiftUpπ A))

/-- The upward sequence functor evaluates to the upward short exact sequence. -/
@[simp] theorem dimensionShiftUpSESFunctor_obj (A : Rep k G) :
    (dimensionShiftUpSESFunctor (k := k) (G := G)).obj A = dimensionShiftUpSES A :=
  (dimensionShiftUpSES_def A).symm

/-- The upward sequence functor acts on morphisms by `dimensionShiftUpSESMap`. -/
@[simp] theorem dimensionShiftUpSESFunctor_map (f : A ⟶ B) :
    (dimensionShiftUpSESFunctor (k := k) (G := G)).map f = dimensionShiftUpSESMap f := by
  apply ShortComplex.Hom.ext <;>
    simp [dimensionShiftUpSESFunctor, ShortComplex.functorEquivalence,
      ShortComplex.FunctorEquivalence.functor]

/-- The downward dimension shift as an endofunctor on representations. -/
@[expose] def dimensionShiftDownFunctor : Rep k G ⥤ Rep k G where
  obj := dimensionShiftDown
  map := fun f => dimensionShiftDownMap f
  map_id := dimensionShiftDownMap_id
  map_comp := fun f g => dimensionShiftDownMap_comp f g

/-- The downward shift functor evaluates to the downward shift. -/
@[simp] theorem dimensionShiftDownFunctor_obj (A : Rep k G) :
    (dimensionShiftDownFunctor (k := k) (G := G)).obj A = dimensionShiftDown A := rfl

/-- The downward shift functor acts on morphisms by `dimensionShiftDownMap`. -/
@[simp] theorem dimensionShiftDownFunctor_map (f : A ⟶ B) :
    (dimensionShiftDownFunctor (k := k) (G := G)).map f = dimensionShiftDownMap f := rfl

/-- The inclusion of the downward shift into induction, natural in coefficients. -/
@[expose] def dimensionShiftDownιNatTrans : dimensionShiftDownFunctor (k := k) (G := G) ⟶
    indBotRepFunctor (k := k) (G := G) where
  app A := dimensionShiftDownι A
  naturality := by
    intro A B f
    simpa only [dimensionShiftDownFunctor_obj, indBotRepFunctor_obj,
      dimensionShiftDownFunctor_map, indBotRepFunctor_map] using
      dimensionShiftDownι_naturality f

/-- The component of the downward inclusion is the kernel inclusion. -/
@[simp] theorem dimensionShiftDownιNatTrans_app (A : Rep k G) :
    (dimensionShiftDownιNatTrans (k := k) (G := G)).app A = dimensionShiftDownι A := rfl

/-- The downward short exact sequence as a functor of coefficient representations. -/
@[expose] def dimensionShiftDownSESFunctor : Rep k G ⥤ ShortComplex (Rep k G) :=
  (ShortComplex.functorEquivalence (Rep k G) (Rep k G)).functor.obj
    (ShortComplex.mk (dimensionShiftDownιNatTrans (k := k) (G := G))
      (indBotCounitNatTrans (k := k) (G := G)) (by
        apply NatTrans.ext
        funext A
        simp only [NatTrans.comp_app, zero_app, dimensionShiftDownιNatTrans_app,
          indBotCounitNatTrans_app]
        exact dimensionShiftDownι_comp_indBotCounit A))

/-- The downward sequence functor evaluates to the downward short exact sequence. -/
@[simp] theorem dimensionShiftDownSESFunctor_obj (A : Rep k G) :
    (dimensionShiftDownSESFunctor (k := k) (G := G)).obj A = dimensionShiftDownSES A :=
  (dimensionShiftDownSES_def A).symm

/-- The downward sequence functor acts on morphisms by `dimensionShiftDownSESMap`. -/
@[simp] theorem dimensionShiftDownSESFunctor_map (f : A ⟶ B) :
    (dimensionShiftDownSESFunctor (k := k) (G := G)).map f = dimensionShiftDownSESMap f := by
  apply ShortComplex.Hom.ext <;>
    simp [dimensionShiftDownSESFunctor, ShortComplex.functorEquivalence,
      ShortComplex.FunctorEquivalence.functor]

end Rep
