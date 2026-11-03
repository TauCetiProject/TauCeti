/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Adjunction.Reflective
public import Mathlib.CategoryTheory.Monad.Limits
public import TauCeti.Algebra.Category.ModuleCat.Smooth.Basic

/-!
# The smooth part of a module

Let `A` be a ring and `J : ι → Submodule A A` a nonempty family of left ideals that is directed
downwards. The *smooth part* of an `A`-module `M` is its largest submodule which is smooth for `J`
(`TauCeti.smoothModules`). Every linear map sends smooth parts into smooth parts, so the smooth part
is a functor from all `A`-modules to smooth `A`-modules, and it is right adjoint to the inclusion of
the smooth modules. Hence the smooth modules form a coreflective full subcategory of `ModuleCat A`
and have all limits: the product of a family of smooth modules in this subcategory is the smooth
part of their ordinary product, which is generally smaller.

A vector `m` lies in the smooth part exactly when its cyclic submodule `A ∙ m` is smooth. When the
family is stable under right multiplication (for each `b` and `i` some `J j` satisfies
`J j * b ⊆ J i`), this is simply the condition that `m` is killed by some `J i`. For the left ideals
of a topological ring with continuous right multiplications forming a basis of neighborhoods of
`0`, this stability holds automatically.

## Main definitions

* `TauCeti.smoothPart J M`: the supremum of the submodules of `M` all of whose vectors are killed
  by some `J i`; for nonempty directed `J`, the largest such submodule.
* `TauCeti.smoothPartFunctor hJ`: the smooth part as a functor `ModuleCat A ⥤ smooth modules`.
* `TauCeti.smoothPartAdjunction hJ`: the inclusion of smooth modules is left adjoint to the smooth
  part.

## Main results

* `TauCeti.mem_smoothPart_iff`: `m` lies in the smooth part when `A ∙ m` is smooth.
* `TauCeti.mem_smoothPart_iff_of_mul_mem`, `TauCeti.mem_smoothPart_iff_of_hasBasis`: under right
  multiplication stability, `m` lies in the smooth part when some `J i` kills it.
* `TauCeti.smoothPart_eq_top_iff`: a module is smooth when it is its own smooth part.
* `TauCeti.hasLimitsOfSize_smoothModules`: the smooth modules have all limits.

## References

* Edward Frenkel, *Langlands Correspondence for Loop Groups*, Cambridge Studies in Advanced
  Mathematics 103, Cambridge University Press, 2007, Section 2.1, for smooth modules over the
  completed enveloping algebra of an affine Lie algebra.
-/

public section

namespace TauCeti

open CategoryTheory Limits Topology Filter

universe t v w u

variable {A : Type u} [Ring A] {ι : Type*} (J : ι → Submodule A A)

/-! ### The smooth part of a module -/

section SmoothPart

variable (M : Type v) [AddCommGroup M] [Module A M] {N : Type*} [AddCommGroup N] [Module A N]

/-- The *smooth part* of an `A`-module `M` for a family `J` of left ideals: the supremum of the
submodules of `M` all of whose vectors are killed by some `J i`. When `J` is nonempty and directed
downwards, it is the largest such submodule (`le_smoothPart_iff`). -/
def smoothPart : Submodule A M :=
  sSup {p | ∀ m ∈ p, ∃ i, ∀ a ∈ J i, a • m = 0}

variable {J M}

/-- A submodule all of whose vectors are killed by some `J i` lies in the smooth part. -/
theorem le_smoothPart {p : Submodule A M} (hp : ∀ m ∈ p, ∃ i, ∀ a ∈ J i, a • m = 0) :
    p ≤ smoothPart J M :=
  le_sSup hp

/-- Linear maps send smooth parts into smooth parts. -/
theorem map_smoothPart_le (f : M →ₗ[A] N) : (smoothPart J M).map f ≤ smoothPart J N := by
  refine Submodule.map_le_iff_le_comap.2 (sSup_le fun p hp => Submodule.map_le_iff_le_comap.1 ?_)
  refine le_smoothPart ?_
  rintro _ ⟨m, hm, rfl⟩
  obtain ⟨i, hi⟩ := hp m hm
  exact ⟨i, fun a ha => by rw [← map_smul, hi a ha, map_zero]⟩

variable [Nonempty ι]

/-- For a directed family `J`, every vector of the smooth part is killed by some `J i`. -/
theorem exists_forall_smul_eq_zero_of_mem_smoothPart (hJ : Directed (· ≥ ·) J) {m : M}
    (hm : m ∈ smoothPart J M) : ∃ i, ∀ a ∈ J i, a • m = 0 := by
  rw [smoothPart, sSup_eq_iSup'] at hm
  refine Submodule.iSup_induction _ (motive := fun m => ∃ i, ∀ a ∈ J i, a • m = 0) hm
    (fun p m hm => p.2 m hm) ⟨Classical.arbitrary ι, fun a _ => smul_zero a⟩ ?_
  rintro x y ⟨i, hi⟩ ⟨j, hj⟩
  obtain ⟨k, hik, hjk⟩ := hJ i j
  exact ⟨k, fun a ha => by rw [smul_add, hi a (hik ha), hj a (hjk ha), add_zero]⟩

/-- For a directed family `J`, a vector lies in the smooth part exactly when its cyclic submodule
is smooth: every `b • m` is killed by some `J i`. -/
theorem mem_smoothPart_iff (hJ : Directed (· ≥ ·) J) {m : M} :
    m ∈ smoothPart J M ↔ ∀ b : A, ∃ i, ∀ a ∈ J i, a • b • m = 0 := by
  refine ⟨fun hm b => exists_forall_smul_eq_zero_of_mem_smoothPart hJ
    ((smoothPart J M).smul_mem b hm), fun h => ?_⟩
  refine le_smoothPart (p := A ∙ m) ?_ (Submodule.mem_span_singleton_self m)
  rintro _ hm
  obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.1 hm
  exact h b

/-- For a directed family `J`, the smooth part is the largest submodule all of whose vectors are
killed by some `J i`. -/
theorem le_smoothPart_iff (hJ : Directed (· ≥ ·) J) {p : Submodule A M} :
    p ≤ smoothPart J M ↔ ∀ m ∈ p, ∃ i, ∀ a ∈ J i, a • m = 0 :=
  ⟨fun hp _ hm => exists_forall_smul_eq_zero_of_mem_smoothPart hJ (hp hm), le_smoothPart⟩

/-- If the directed family `J` is stable under right multiplication, in the sense that for every
`b` and `i` some `J j` satisfies `J j * b ⊆ J i`, a vector lies in the smooth part exactly when it
is killed by some `J i`. -/
theorem mem_smoothPart_iff_of_mul_mem (hJ : Directed (· ≥ ·) J)
    (hJb : ∀ (b : A) i, ∃ j, ∀ a ∈ J j, a * b ∈ J i) {m : M} :
    m ∈ smoothPart J M ↔ ∃ i, ∀ a ∈ J i, a • m = 0 := by
  refine ⟨exists_forall_smul_eq_zero_of_mem_smoothPart hJ, fun ⟨i, hi⟩ => ?_⟩
  refine (mem_smoothPart_iff hJ).2 fun b => ?_
  obtain ⟨j, hj⟩ := hJb b i
  exact ⟨j, fun a ha => by rw [← mul_smul, hi _ (hj a ha)]⟩

/-- For a directed family `J`, a module is smooth exactly when it is its own smooth part. -/
theorem smoothPart_eq_top_iff (hJ : Directed (· ≥ ·) J) :
    smoothPart J M = ⊤ ↔ smoothModules.{v} J (ModuleCat.of A M) := by
  rw [smoothModules_iff]
  exact ⟨fun h m => exists_forall_smul_eq_zero_of_mem_smoothPart hJ (h ▸ Submodule.mem_top),
    fun h => eq_top_iff.2 (le_smoothPart fun m _ => h m)⟩

/-- For a directed family `J`, the smooth part of a module is a smooth module. -/
theorem smoothModules_smoothPart (hJ : Directed (· ≥ ·) J) :
    smoothModules.{v} J (ModuleCat.of A (smoothPart J M)) := smoothModules_iff.2 fun m => by
  obtain ⟨i, hi⟩ := exists_forall_smul_eq_zero_of_mem_smoothPart hJ m.2
  exact ⟨i, fun a ha => Subtype.ext (hi a ha)⟩

end SmoothPart

/-! ### Left ideals of a topological ring -/

section Topological

variable [TopologicalSpace A] [SeparatelyContinuousMul A] {J}

/-- If the left ideals `J i` form a basis of neighborhoods of `0` and right multiplications are
continuous, then for every `b` and `i` some `J j` satisfies `J j * b ⊆ J i`. -/
theorem exists_forall_mul_mem_of_hasBasis
    (hJ : (𝓝 (0 : A)).HasBasis (fun _ => True) fun i => (J i : Set A)) (b : A) (i : ι) :
    ∃ j, ∀ a ∈ J j, a * b ∈ J i := by
  have : Tendsto (· * b) (𝓝 (0 : A)) (𝓝 0) := by
    simpa using (continuous_mul_const b).tendsto (0 : A)
  obtain ⟨j, -, hj⟩ := hJ.mem_iff.1 (this (hJ.mem_of_mem (i := i) trivial))
  exact ⟨j, fun a ha => hj ha⟩

/-- If the left ideals `J i` form a basis of neighborhoods of `0` and right multiplications are
continuous, a vector lies in the smooth part exactly when it is killed by some `J i`. -/
theorem mem_smoothPart_iff_of_hasBasis [Nonempty ι]
    (hJ : (𝓝 (0 : A)).HasBasis (fun _ => True) fun i => (J i : Set A)) {M : Type*}
    [AddCommGroup M] [Module A M] {m : M} :
    m ∈ smoothPart J M ↔ ∃ i, ∀ a ∈ J i, a • m = 0 := by
  refine mem_smoothPart_iff_of_mul_mem (fun i j => ?_) (exists_forall_mul_mem_of_hasBasis hJ)
  obtain ⟨k, -, hk⟩ := hJ.mem_iff.1 (inter_mem (hJ.mem_of_mem (i := i) trivial)
    (hJ.mem_of_mem (i := j) trivial))
  exact ⟨k, fun _ ha => (hk ha).1, fun _ ha => (hk ha).2⟩

end Topological

/-! ### The coreflection onto smooth modules -/

section Coreflection

variable {J} [Nonempty ι]

/-- For a directed family `J`, the smooth part as a functor from `A`-modules to smooth
`A`-modules. -/
@[expose]
noncomputable def smoothPartFunctor (hJ : Directed (· ≥ ·) J) :
    ModuleCat.{v} A ⥤ (smoothModules.{v} J).FullSubcategory where
  obj M := ⟨ModuleCat.of A (smoothPart J M), smoothModules_smoothPart hJ⟩
  map f := ObjectProperty.homMk (ModuleCat.ofHom (f.hom.restrict fun m hm =>
    map_smoothPart_le f.hom (Submodule.mem_map_of_mem hm)))

/-- The smooth part functor sends a module to its smooth part. -/
@[simp]
theorem smoothPartFunctor_obj_obj (hJ : Directed (· ≥ ·) J) (M : ModuleCat.{v} A) :
    ((smoothPartFunctor hJ).obj M).obj = ModuleCat.of A (smoothPart J M) :=
  rfl

/-- The smooth part of a linear map is its restriction. -/
@[simp]
theorem smoothPartFunctor_map_hom (hJ : Directed (· ≥ ·) J) {M N : ModuleCat.{v} A}
    (f : M ⟶ N) :
    ((smoothPartFunctor hJ).map f).hom = ModuleCat.ofHom (f.hom.restrict fun _ hm =>
      map_smoothPart_le f.hom (Submodule.mem_map_of_mem hm)) :=
  rfl

/-- For a directed family `J`, the inclusion of smooth `A`-modules is left adjoint to the smooth
part: linear maps from a smooth module `N` to `M` are the linear maps from `N` to the smooth part
of `M`. The counit is the inclusion of the smooth part. -/
@[expose, simps! unit_app counit_app]
noncomputable def smoothPartAdjunction (hJ : Directed (· ≥ ·) J) :
    (smoothModules.{v} J).ι ⊣ smoothPartFunctor hJ :=
  Adjunction.mkOfUnitCounit
    { unit :=
        { app N := ObjectProperty.homMk (ModuleCat.ofHom (LinearMap.codRestrict _ LinearMap.id
            fun n => le_smoothPart (p := ⊤) (fun m _ => smoothModules_iff.1 N.property m)
              Submodule.mem_top)) }
      counit := { app M := ModuleCat.ofHom (smoothPart J M).subtype } }

/-- For a directed family `J`, the inclusion of smooth `A`-modules is coreflective, with
coreflector the smooth part. -/
@[expose, instance_reducible]
noncomputable def coreflectiveSmoothModules (hJ : Directed (· ≥ ·) J) :
    Coreflective (smoothModules.{v} J).ι where
  R := smoothPartFunctor hJ
  adj := smoothPartAdjunction hJ

/-- For a directed family `J`, the smooth `A`-modules have all limits. A limit of smooth modules
can be computed as the smooth part of their limit in `ModuleCat A`. -/
theorem hasLimitsOfSize_smoothModules [UnivLE.{w, v}] (hJ : Directed (· ≥ ·) J) :
    HasLimitsOfSize.{t, w} (smoothModules.{v} J).FullSubcategory :=
  letI := coreflectiveSmoothModules hJ
  haveI : HasLimitsOfSize.{t, w} (ModuleCat.{v} A) := ModuleCat.hasLimitsOfSize
  hasLimits_of_coreflective (smoothModules.{v} J).ι

end Coreflection

end TauCeti
