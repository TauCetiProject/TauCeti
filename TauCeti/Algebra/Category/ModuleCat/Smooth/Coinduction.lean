/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.Algebra.Category.ModuleCat.Injective
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.RingTheory.SimpleModule.InjectiveProjective
public import TauCeti.Algebra.Category.ModuleCat.Smooth.Coreflection

/-!
# Continuous coinduction and enough injectives for smooth modules

Let `f : R →+* A` be a ring homomorphism and `J : ι → Submodule A A` a nonempty family of left
ideals of `A` that is directed downwards. The *coinduction* of an `R`-module `V` is the smooth part
(`TauCeti.smoothPart`) of Mathlib's coextension of scalars `Hom_R(A, V)`, on which `A` acts by
`(b • g) a = g (a * b)`. It is right adjoint to the functor sending a smooth `A`-module to its
underlying `R`-module, obtained by composing Mathlib's `ModuleCat.restrictCoextendScalarsAdj` with
the smooth-part coreflection.

A left ideal `I` kills `g : Hom_R(A, V)` exactly when `I ⊆ ker g`. Hence, when the family `J` is
also stable under right multiplication, `g` lies in the coinduction exactly when its kernel
contains some `J i`. When the `J i` form a basis of neighborhoods of `0` in a topological ring,
this says that `g` is continuous for the discrete topology on `V`, so that the coinduction is the
module `Hom_cont,R(A, V)` of continuous `R`-linear maps.

The underlying-module functor is faithful and preserves monomorphisms, so the coinduction
preserves injective objects; over a semisimple ring `R`, such as a field, every coinduced module
is injective. The unit of the adjunction is the injective map `m ↦ (a ↦ a • m)`, so coinduction
along `ℤ →+* A` shows that the category of smooth `A`-modules has enough injectives. Consequently
the smooth modules over `A : Type u`, with modules in universe `max u w`, have `Ext` groups in the
universe `max u w` of their morphisms, so derived functors of smooth modules can be computed
with injective resolutions.

## Main definitions

* `TauCeti.coinduction f hJ`: the functor from `R`-modules to smooth `A`-modules sending `V` to
  the smooth part of its coextension of scalars `Hom_R(A, V)`; this is `Hom_cont,R(A, V)` when the
  `J i` form a basis of neighborhoods of `0`.
* `TauCeti.coinductionAdjunction f hJ`: the underlying `R`-module functor of smooth `A`-modules is
  left adjoint to the coinduction.

## Main results

* `TauCeti.mem_smoothPart_coextendScalars_iff`: `g` lies in the coinduction when some `J i` lies
  in its kernel.
* `TauCeti.mem_smoothPart_coextendScalars_iff_continuous`: for a basis of neighborhoods of `0`,
  `g` lies in the coinduction when it is continuous for the discrete topology on `V`.
* `TauCeti.coinductionAdjunction_unit_app_injective`: the unit `m ↦ (a ↦ a • m)` is injective.
* `TauCeti.injective_coinduction_obj`: coinduction preserves injective objects.
* `TauCeti.enoughInjectives_smoothModules`: smooth modules have enough injectives.
* `TauCeti.hasExt_smoothModules`: smooth modules have `Ext` groups in the universe of morphisms.

## References

* Edward Frenkel, *Langlands Correspondence for Loop Groups*, Cambridge Studies in Advanced
  Mathematics 103, Cambridge University Press, 2007, Section 2.1, for smooth modules over the
  completed enveloping algebra of an affine Lie algebra.
* Jean-Pierre Serre, *Galois Cohomology*, Springer, 1997, Chapter I, Section 2.5, for the
  analogous coinduced discrete modules of continuous maps out of a profinite group.
-/

public section

namespace TauCeti

open CategoryTheory Limits Topology Filter

universe w u₁ u

variable {R : Type u₁} {A : Type u} [Ring R] [Ring A] (f : R →+* A) {ι : Type*}
  {J : ι → Submodule A A}

/-! ### Smooth vectors of the coextension of scalars -/

section Coextension

variable {f} {V : ModuleCat R}

/-- A left ideal `I` kills an `R`-linear map `g : A → V` of the coextension of scalars exactly
when `I` lies in the kernel of `g`. -/
theorem forall_smul_coextendScalars_eq_zero_iff (I : Submodule A A)
    (g : (ModuleCat.coextendScalars f).obj V) : (∀ a ∈ I, a • g = 0) ↔ ∀ a ∈ I, g a = 0 := by
  refine ⟨fun h a ha => ?_, fun h a ha =>
    ModuleCat.CoextendScalars.ext (LinearMap.ext fun (s : A) => ?_)⟩
  · -- Evaluating `a • g = 0` at `1` gives `g a = 0`.
    have := congr($(h a ha) (1 : A))
    rwa [ModuleCat.CoextendScalars.smul_apply, one_mul] at this
  · exact (ModuleCat.CoextendScalars.smul_apply _ _ _ _ s).trans (h _ (I.smul_mem s ha))

/-- If the directed family `J` is stable under right multiplication, an `R`-linear map
`g : A → V` lies in the smooth part of the coextension of scalars exactly when some `J i` lies in
its kernel. -/
theorem mem_smoothPart_coextendScalars_iff [Nonempty ι] (hJ : Directed (· ≥ ·) J)
    (hJb : ∀ (b : A) i, ∃ j, ∀ a ∈ J j, a * b ∈ J i) {g : (ModuleCat.coextendScalars f).obj V} :
    g ∈ smoothPart J ((ModuleCat.coextendScalars f).obj V) ↔ ∃ i, ∀ a ∈ J i, g a = 0 :=
  (mem_smoothPart_iff_of_mul_mem hJ hJb).trans
    (exists_congr fun i => forall_smul_coextendScalars_eq_zero_iff (J i) g)

/-- If the left ideals `J i` form a basis of neighborhoods of `0` in a topological ring, an
`R`-linear map `g : A → V` lies in the smooth part of the coextension of scalars exactly when it is
continuous for the discrete topology on `V`. -/
theorem mem_smoothPart_coextendScalars_iff_continuous [TopologicalSpace A]
    [SeparatelyContinuousAdd A] [SeparatelyContinuousMul A] [Nonempty ι]
    (hJ : (𝓝 (0 : A)).HasBasis (fun _ => True) fun i => (J i : Set A))
    {g : (ModuleCat.coextendScalars f).obj V} :
    g ∈ smoothPart J ((ModuleCat.coextendScalars f).obj V) ↔
      letI : TopologicalSpace V := ⊥; Continuous fun a : A => g a := by
  let : TopologicalSpace V := ⊥
  have : DiscreteTopology V := ⟨rfl⟩
  rw [mem_smoothPart_iff_of_hasBasis hJ, continuous_discrete_rng]
  simp only [forall_smul_coextendScalars_eq_zero_iff]
  refine ⟨fun ⟨i, hi⟩ v => isOpen_iff_mem_nhds.2 fun a₀ (ha₀ : g a₀ = v) => ?_, fun h => ?_⟩
  · -- The translate `a₀ + J i` is an open neighborhood of `a₀` on which `g` takes the value `v`.
    have hJi : IsOpen (J i : Set A) :=
      (J i).toAddSubgroup.isOpen_of_mem_nhds (hJ.mem_of_mem (i := i) trivial)
    refine mem_of_superset ((hJi.preimage (continuous_add_const (-a₀))).mem_nhds (by simp))
      fun a ha => ?_
    -- `g` is additive on `A`, so `g a = g (a - a₀) + g a₀ = v`. The domain of `g` is the
    -- restriction of scalars of `A`, which is `A` only up to unfolding; the `change`s restate the
    -- hypotheses through the additive map `φ` on `A` so that `map_add` applies.
    let φ : A →+ V := (ModuleCat.CoextendScalars.equiv f V g).toAddMonoidHom
    have := hi (a + -a₀) ha
    change φ (a + -a₀) = 0 at this
    change φ a₀ = v at ha₀
    change φ a = v
    rw [map_add, map_neg, add_neg_eq_zero] at this
    exact this.trans ha₀
  · obtain ⟨i, -, hi⟩ := hJ.mem_iff.1 ((h 0).mem_nhds (map_zero _))
    exact ⟨i, fun a ha => hi ha⟩

end Coextension

/-! ### The coinduction functor and its adjunction -/

section Coinduction

variable [Nonempty ι]

/-- The *coinduction* of `R`-modules to smooth `A`-modules along `f : R →+* A`: the smooth part of
the coextension of scalars `Hom_R(A, V)`, which is the module of continuous `R`-linear maps
`A → V` when the `J i` form a basis of neighborhoods of `0`
(`TauCeti.mem_smoothPart_coextendScalars_iff_continuous`). -/
@[expose]
noncomputable def coinduction (hJ : Directed (· ≥ ·) J) :
    ModuleCat.{max u w} R ⥤ (smoothModules.{max u w} J).FullSubcategory :=
  ModuleCat.coextendScalars f ⋙ smoothPartFunctor hJ

/-- The coinduction of `V` is the smooth part of the coextension of scalars of `V`. -/
@[simp]
theorem coinduction_obj_obj (hJ : Directed (· ≥ ·) J) (V : ModuleCat.{max u w} R) :
    ((coinduction f hJ).obj V).obj =
      ModuleCat.of A (smoothPart J ((ModuleCat.coextendScalars f).obj V)) :=
  rfl

/-- The coinduction of a linear map `φ` is postcomposition with `φ`. -/
theorem coinduction_map_hom_apply (hJ : Directed (· ≥ ·) J) {V W : ModuleCat.{max u w} R}
    (φ : V ⟶ W) (g : smoothPart J ((ModuleCat.coextendScalars f).obj V)) (a : A) :
    (((coinduction f hJ).map φ).hom.hom g).1 a = φ ((g : (ModuleCat.coextendScalars f).obj V) a) :=
  rfl

/-- The underlying `R`-module functor of smooth `A`-modules is left adjoint to the coinduction:
`R`-linear maps from a smooth `A`-module `M` to `V` are the `A`-linear maps from `M` to the
smooth part of the coextension of scalars `Hom_R(A, V)`, which is the module of continuous
`R`-linear maps `A → V` when the `J i` form a basis of neighborhoods of `0`. -/
noncomputable def coinductionAdjunction (hJ : Directed (· ≥ ·) J) :
    (smoothModules.{max u w} J).ι ⋙ ModuleCat.restrictScalars.{max u w} f ⊣ coinduction f hJ :=
  (smoothPartAdjunction hJ).comp (ModuleCat.restrictCoextendScalarsAdj f)

/-- The unit of the coinduction adjunction sends `m` to the orbit map `a ↦ a • m`. -/
theorem coinductionAdjunction_unit_app_apply (hJ : Directed (· ≥ ·) J)
    (M : (smoothModules.{max u w} J).FullSubcategory) (m : M.obj) (a : A) :
    (((coinductionAdjunction f hJ).unit.app M).hom.hom m).1 a = a • m :=
  (rfl)

/-- The counit of the coinduction adjunction is evaluation at `1`. -/
theorem coinductionAdjunction_counit_app_apply (hJ : Directed (· ≥ ·) J)
    (V : ModuleCat.{max u w} R) (g : smoothPart J ((ModuleCat.coextendScalars f).obj V)) :
    ((coinductionAdjunction f hJ).counit.app V).hom g = g.1 (1 : A) :=
  (rfl)

/-- The `A`-linear map to the coinduction corresponding to an `R`-linear map `φ : M → V` sends
`m` to `a ↦ φ (a • m)`. -/
theorem coinductionAdjunction_homEquiv_apply_apply (hJ : Directed (· ≥ ·) J)
    {M : (smoothModules.{max u w} J).FullSubcategory} {V : ModuleCat.{max u w} R}
    (φ : ((smoothModules.{max u w} J).ι ⋙ ModuleCat.restrictScalars.{max u w} f).obj M ⟶ V)
    (m : M.obj) (a : A) :
    (((coinductionAdjunction f hJ).homEquiv M V φ).hom.hom m).1 a = φ.hom (a • m : M.obj) :=
  (rfl)

/-- The `R`-linear map corresponding to an `A`-linear map `ψ` to the coinduction is evaluation of
`ψ` at `1`. -/
theorem coinductionAdjunction_homEquiv_symm_apply (hJ : Directed (· ≥ ·) J)
    {M : (smoothModules.{max u w} J).FullSubcategory} {V : ModuleCat.{max u w} R}
    (ψ : M ⟶ (coinduction f hJ).obj V) (m : M.obj) :
    (((coinductionAdjunction f hJ).homEquiv M V).symm ψ).hom m = (ψ.hom.hom m).1 (1 : A) :=
  (rfl)

/-- The unit `m ↦ (a ↦ a • m)` of the coinduction adjunction is injective, by evaluation at
`1`. -/
theorem coinductionAdjunction_unit_app_injective (hJ : Directed (· ≥ ·) J)
    (M : (smoothModules.{max u w} J).FullSubcategory) :
    Function.Injective ((coinductionAdjunction f hJ).unit.app M).hom.hom := fun m n h => by
  have := congr($h.1 (1 : A))
  rwa [coinductionAdjunction_unit_app_apply, coinductionAdjunction_unit_app_apply, one_smul,
    one_smul] at this

/-- Coinduction sends injective `R`-modules to injective smooth `A`-modules, since its left adjoint,
the underlying `R`-module functor, preserves monomorphisms. -/
theorem injective_coinduction_obj (hJ : Directed (· ≥ ·) J) (V : ModuleCat.{max u w} R)
    (hV : Injective V) : Injective ((coinduction f hJ).obj V) :=
  (coinductionAdjunction f hJ).map_injective V hV

/-- Over a semisimple ring `R`, for instance a field, every `R`-module is injective, so the
coinduction of every `R`-module is an injective smooth `A`-module. -/
theorem injective_coinduction_obj_of_isSemisimpleRing [IsSemisimpleRing R]
    (hJ : Directed (· ≥ ·) J) (V : ModuleCat.{max u w} R) :
    Injective ((coinduction f hJ).obj V) :=
  have := Module.injective_of_isSemisimpleRing R V
  injective_coinduction_obj f hJ V (Module.injective_object_of_injective_module R V)

end Coinduction

/-! ### Enough injectives and `Ext` -/

section EnoughInjectives

variable [Nonempty ι]

/-- For a directed family `J` of left ideals of `A : Type u`, the smooth `A`-modules in universe
`max u w` have enough injectives: every smooth module embeds, through the unit of the coinduction
adjunction along `ℤ →+* A`, into the coinduction of an injective abelian group. -/
theorem enoughInjectives_smoothModules (hJ : Directed (· ≥ ·) J) :
    EnoughInjectives (smoothModules.{max u w} J).FullSubcategory :=
  EnoughInjectives.of_adjunction (coinductionAdjunction (Int.castRingHom A) hJ)

/-- For a directed family `J` of left ideals of `A : Type u`, the abelian category of smooth
`A`-modules in universe `max u w` has `Ext` groups in the universe `max u w` of its morphisms.
This holds for any abelian structure on the smooth modules, for instance the one inherited from
`ModuleCat A` through `TauCeti.isClosedUnderFiniteLimits_smoothModules`. -/
theorem hasExt_smoothModules (hJ : Directed (· ≥ ·) J)
    [Abelian (smoothModules.{max u w} J).FullSubcategory] :
    HasExt.{max u w} (smoothModules.{max u w} J).FullSubcategory :=
  have := enoughInjectives_smoothModules.{w} hJ
  hasExt_of_enoughInjectives.{max u w} _

end EnoughInjectives

end TauCeti
