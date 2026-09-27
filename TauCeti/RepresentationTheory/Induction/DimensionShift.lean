/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude, Codex
-/
module

import TauCeti.Algebra.Homology.ShortComplex.ShortExact
import TauCeti.RepresentationTheory.Rep.TensorShortExact

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
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
* `Rep.dimensionShiftUpMap`, `Rep.dimensionShiftDownMap`: the maps on both shifts induced by a
  morphism of coefficient representations.

## Main statements

* `Rep.dimensionShiftUpSES_def`, `Rep.dimensionShiftDownSES_def`: the maps in the two short
  complexes.
* `Rep.dimensionShiftUpSES_shortExact`, `Rep.dimensionShiftUpSES_res_shortExact`,
  `Rep.dimensionShiftUpSES_tensorLeft_shortExact`: the upward sequence is short exact, also after
  restriction and after tensoring on the left with any representation.
* `Rep.dimensionShiftDownSES_shortExact`, `Rep.dimensionShiftDownSES_res_shortExact`,
  `Rep.dimensionShiftDownSES_tensorLeft_shortExact`: the same for the downward sequence.
* `Rep.dimensionShiftUpSESMap`, `Rep.dimensionShiftDownSESMap`: morphisms of the two short exact
  sequences; their commuting squares identify the induced maps on kernels and cokernels.

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
  have hr : Function.LeftInverse (LinearMap.proj 1 ∘ₗ (coindBotEquivPi k G A.V).toLinearMap)
      (coindBotUnit A).hom := fun a ↦ by
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, coindBotEquivPi_apply, LinearMap.proj_apply,
      coindBotUnit_hom_apply_coe, map_one, Module.End.one_apply]
  have : Epi (dimensionShiftUpSES A).g := (dimensionShiftUpSES_shortExact A).epi_g
  exact shortExact_map_tensorLeft_of_leftInverse (dimensionShiftUpSES_shortExact A).exact M _ hr

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

/-! ### Naturality of the dimension-shifting sequences -/

variable {A B : Rep k G}

/-- The coinduction map induced by a morphism of representations on the underlying modules. -/
def coindBotMap (f : A ⟶ B) : coindBot k G A.V ⟶ coindBot k G B.V :=
  (coindBotFunctor k G).map (ModuleCat.ofHom f.hom)

/-- The orbit-map embedding into coinduction is natural in the representation. -/
theorem coindBotUnit_naturality (f : A ⟶ B) :
    coindBotUnit A ≫ coindBotMap f = f ≫ coindBotUnit B := by
  ext x g
  calc
    _ = ((coindBotMap f).hom ((coindBotUnit A).hom x)).1 g := by
      exact congrArg (fun z : coindBot k G B.V => z.1 g)
        (CategoryTheory.comp_apply (coindBotUnit A) (coindBotMap f) x)
    _ = f.hom (A.ρ g x) := by
      -- The coinduction functor acts pointwise; make the underlying function visible.
      change f.hom (((coindBotUnit A).hom x).1 g) = f.hom (A.ρ g x)
      rw [coindBotUnit_hom_apply_coe]
    _ = B.ρ g (f.hom x) := Rep.hom_comm_apply f g x
    _ = ((coindBotUnit B).hom (f.hom x)).1 g := by rw [coindBotUnit_hom_apply_coe]
    _ = _ := by
      exact (congrArg (fun z : coindBot k G B.V => z.1 g)
        (CategoryTheory.comp_apply f (coindBotUnit B) x)).symm

/-- The morphism on the upward dimension shift induced by a representation morphism. -/
def dimensionShiftUpMap (f : A ⟶ B) : dimensionShiftUp A ⟶ dimensionShiftUp B :=
  cokernel.map (coindBotUnit A) (coindBotUnit B) f (coindBotMap f)
    (coindBotUnit_naturality f)

/-- The upward shift map commutes with the quotient from coinduction. -/
@[reassoc (attr := simp)]
theorem dimensionShiftUpπ_naturality (f : A ⟶ B) :
    dimensionShiftUpπ A ≫ dimensionShiftUpMap f =
      coindBotMap f ≫ dimensionShiftUpπ B := by
  unfold dimensionShiftUpπ dimensionShiftUpMap cokernel.map
  exact cokernel.π_desc _ _ _

/-- A morphism of representations acts on the upward dimension-shifting short exact sequence. -/
def dimensionShiftUpSESMap (f : A ⟶ B) :
    ShortComplex.mk (coindBotUnit A) (dimensionShiftUpπ A)
        (coindBotUnit_comp_dimensionShiftUpπ A) ⟶
      ShortComplex.mk (coindBotUnit B) (dimensionShiftUpπ B)
        (coindBotUnit_comp_dimensionShiftUpπ B) :=
  { τ₁ := f
    τ₂ := coindBotMap f
    τ₃ := dimensionShiftUpMap f
    comm₁₂ := (coindBotUnit_naturality f).symm
    comm₂₃ := (dimensionShiftUpπ_naturality f).symm }

/-- The first component of the upward sequence map is the original morphism. -/
@[simp]
theorem dimensionShiftUpSESMap_τ₁ (f : A ⟶ B) :
    (dimensionShiftUpSESMap f).τ₁ = f := by
  simp [dimensionShiftUpSESMap]

/-- The middle component of the upward sequence map is the coinduction map. -/
@[simp]
theorem dimensionShiftUpSESMap_τ₂ (f : A ⟶ B) :
    (dimensionShiftUpSESMap f).τ₂ = coindBotMap f := by simp [dimensionShiftUpSESMap]

/-- The last component of the upward sequence map is the induced shift morphism. -/
@[simp]
theorem dimensionShiftUpSESMap_τ₃ (f : A ⟶ B) :
    (dimensionShiftUpSESMap f).τ₃ = dimensionShiftUpMap f := by simp [dimensionShiftUpSESMap]

/-- The induction map induced by a morphism on the underlying coefficient modules. -/
def indBotMap (f : A ⟶ B) : indBot k G A.V ⟶ indBot k G B.V := by
  rw [← indBotFunctor_obj (X := ModuleCat.of k A.V),
    ← indBotFunctor_obj (X := ModuleCat.of k B.V)]
  exact (indBotFunctor k G).map (ModuleCat.ofHom f.hom)

/-- The projection from induction onto the representation is natural. -/
theorem indBotCounit_naturality (f : A ⟶ B) :
    indBotMap f ≫ indBotCounit B = indBotCounit A ≫ f := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply Representation.IndV.hom_ext
  intro g
  apply LinearMap.ext
  intro x
  calc
    _ = (indBotCounit B).hom ((indBotMap f).hom
        (Representation.IndV.mk (⊥ : Subgroup G).subtype
          (Representation.trivial k (⊥ : Subgroup G) A.V) g x)) :=
      CategoryTheory.comp_apply (indBotMap f) (indBotCounit B) _
    _ = B.ρ g⁻¹ (f.hom x) := by
      -- The transported functor map evaluates on induced generators pointwise.
      change (indBotCounit B).hom
        (Representation.IndV.mk (⊥ : Subgroup G).subtype
          (Representation.trivial k (⊥ : Subgroup G) B.V) g (f.hom x)) = _
      rw [indBotCounit_hom_mk]
    _ = f.hom (A.ρ g⁻¹ x) := (Rep.hom_comm_apply f g⁻¹ x).symm
    _ = f.hom ((indBotCounit A).hom
        (Representation.IndV.mk (⊥ : Subgroup G).subtype
          (Representation.trivial k (⊥ : Subgroup G) A.V) g x)) := by
      rw [indBotCounit_hom_mk]
    _ = _ := (CategoryTheory.comp_apply (indBotCounit A) f _).symm

/-- The morphism on the downward dimension shift induced by a representation morphism. -/
def dimensionShiftDownMap (f : A ⟶ B) : dimensionShiftDown A ⟶ dimensionShiftDown B :=
  kernel.map (indBotCounit A) (indBotCounit B) (indBotMap f) f
    (indBotCounit_naturality f).symm

/-- The downward shift map commutes with inclusion into induction. -/
@[reassoc (attr := simp)]
theorem dimensionShiftDownι_naturality (f : A ⟶ B) :
    dimensionShiftDownMap f ≫ dimensionShiftDownι B =
      dimensionShiftDownι A ≫ indBotMap f := by
  unfold dimensionShiftDownMap dimensionShiftDownι
  exact kernel.lift_ι _ _ _

/-- A morphism acts on the downward dimension-shifting short exact sequence. -/
def dimensionShiftDownSESMap (f : A ⟶ B) :
    ShortComplex.mk (dimensionShiftDownι A) (indBotCounit A)
        (dimensionShiftDownι_comp_indBotCounit A) ⟶
      ShortComplex.mk (dimensionShiftDownι B) (indBotCounit B)
        (dimensionShiftDownι_comp_indBotCounit B) :=
  { τ₁ := dimensionShiftDownMap f
    τ₂ := indBotMap f
    τ₃ := f
    comm₁₂ := dimensionShiftDownι_naturality f
    comm₂₃ := indBotCounit_naturality f }

/-- The first component of the downward sequence map is the induced shift morphism. -/
@[simp]
theorem dimensionShiftDownSESMap_τ₁ (f : A ⟶ B) :
    (dimensionShiftDownSESMap f).τ₁ = dimensionShiftDownMap f := by simp [dimensionShiftDownSESMap]

/-- The middle component of the downward sequence map is the induction map. -/
@[simp]
theorem dimensionShiftDownSESMap_τ₂ (f : A ⟶ B) :
    (dimensionShiftDownSESMap f).τ₂ = indBotMap f := by simp [dimensionShiftDownSESMap]

/-- The last component of the downward sequence map is the original morphism. -/
@[simp]
theorem dimensionShiftDownSESMap_τ₃ (f : A ⟶ B) :
    (dimensionShiftDownSESMap f).τ₃ = f := by simp [dimensionShiftDownSESMap]

end Rep
