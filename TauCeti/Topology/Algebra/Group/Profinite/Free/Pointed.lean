/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactification.OnePoint.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProC
public import TauCeti.Topology.Algebra.Group.Profinite.Generation
public import TauCeti.Topology.Algebra.Group.Profinite.Limit

/-!
# The free pro-`C` group on a pointed topological space

For a class `C` of finite groups and a pointed topological space `(X, x₀)`, the **free pro-`C`
group on `(X, x₀)`** is the pro-`C` group `F_C(X, x₀)` with a continuous map `X → F_C(X, x₀)`
sending `x₀` to `1` such that every continuous map `X → P` to a profinite pro-`C` group `P` with
`x₀ ↦ 1` extends uniquely to a continuous homomorphism `F_C(X, x₀) → P`. When `X` is a profinite
space this is the free pro-`C` group on a pointed profinite space of Ribes and Zalesskii, §3.3,
the object on which the infinite-rank theory of free pro-`C` groups is built.

The construction quotients the free pro-`C` group `freeProC C X` on the underlying type of `X` by
the intersection of its **admissible** open normal subgroups, those `U` through which the
generator map `X → freeProC C X ⧸ U` is continuous and kills `x₀`. Nothing in the construction
uses compactness of `X`, so the definitions and theorems are stated for an arbitrary pointed
topological space.

For a discrete `X` the object is the free pro-`C` group on the type `X ∖ {x₀}`. For the one-point
compactification `S⁺` of a space `S`, pointed at `∞`, the inclusion `S → S⁺` induces a continuous
surjection `freeProC C S → F_C(S⁺, ∞)`, and for discrete `S` the images of the points of `S`
converge to `1`.

## Main definitions

* `TauCeti.freeProCPointed`: the free pro-`C` group on a pointed topological space.
* `TauCeti.freeProCPointed.of`: the canonical continuous map from the space.
* `TauCeti.freeProCPointed.lift`: the extension of a base-point-preserving continuous map.
* `TauCeti.freeProCPointed.equivFreeProC`: for a discrete space, the identification with the free
  pro-`C` group on the complement of the base point.
* `TauCeti.freeProCPointed.fromFreeProC`: the surjection from the free pro-`C` group on `S` onto
  the free pro-`C` group on the pointed one-point compactification of `S`.

## Main results

* `TauCeti.isProC_freeProCPointed`: the free pro-`C` group on a pointed space is pro-`C`.
* `TauCeti.freeProCPointed.continuous_of`, `TauCeti.freeProCPointed.of_basePoint`: the canonical
  map is continuous and kills the base point.
* `TauCeti.freeProCPointed.existsUnique_lift`: the universal property.
* `TauCeti.freeProCPointed.dense_closure_range_of`: the image of `X` generates topologically.
* `TauCeti.freeProCPointed.fromFreeProC_surjective`: the free pro-`C` group on a type maps onto
  the free pro-`C` group on its pointed one-point compactification.
* `TauCeti.freeProCPointed.tendsto_of_coe_cofinite_nhds_one`: for a discrete space `S`, the
  images of the points of `S` in `F_C(S⁺, ∞)` converge to `1` along the cofinite filter on `S`.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 3.3.
-/

public section

namespace TauCeti

universe u v w

section Admissible

variable (C : FiniteGroupClass.{w}) {X : Type u} [TopologicalSpace X] (x₀ : X)

namespace freeProCPointed

/-- An open normal subgroup `U` of the free pro-`C` group on the type `X` is **admissible** for
the base point `x₀` when the composite `X → freeProC C X → freeProC C X ⧸ U` is continuous and
sends `x₀` to `1`. The admissible subgroups are exactly the finite-quotient shadows of the
continuous base-point-preserving maps from `X` to pro-`C` groups. -/
def IsAdmissible (U : OpenNormalSubgroup (freeProC C X)) : Prop :=
  Continuous (fun x : X ↦ ((freeProC.of x : freeProC C X) : freeProC C X ⧸ U.toSubgroup)) ∧
    freeProC.of x₀ ∈ U.toSubgroup

/-- The whole group is admissible. -/
private theorem isAdmissible_top : IsAdmissible C x₀ (openNormalSubgroupTop (freeProC C X)) := by
  have : Subsingleton (freeProC C X ⧸ (openNormalSubgroupTop (freeProC C X)).toSubgroup) :=
    QuotientGroup.subsingleton_iff.mpr (openNormalSubgroupTop_toSubgroup _)
  refine ⟨(continuous_const (y := (1 : freeProC C X ⧸ _))).congr fun _ ↦ Subsingleton.elim _ _, ?_⟩
  rw [openNormalSubgroupTop_toSubgroup]
  exact Subgroup.mem_top _

variable {C x₀}

/-- The intersection of two admissible open normal subgroups is admissible. -/
private theorem IsAdmissible.inf {U V : OpenNormalSubgroup (freeProC C X)}
    (hU : IsAdmissible C x₀ U) (hV : IsAdmissible C x₀ V) : IsAdmissible C x₀ (U ⊓ V) :=
  ⟨OpenNormalSubgroup.continuous_mk_inf hU.1 hV.1, Subgroup.mem_inf.mpr ⟨hU.2, hV.2⟩⟩

variable (C x₀)

/-- The kernel of the free pro-`C` group on the pointed space `(X, x₀)`: the intersection of the
admissible open normal subgroups of the free pro-`C` group on the type `X`. -/
noncomputable def kernel : Subgroup (freeProC C X) :=
  ⨅ U : {U : OpenNormalSubgroup (freeProC C X) // IsAdmissible C x₀ U}, U.1.toSubgroup

/-- Membership in the kernel, unfolded over the admissible subgroups. -/
theorem mem_kernel_iff {y : freeProC C X} :
    y ∈ kernel C x₀ ↔
      ∀ U : OpenNormalSubgroup (freeProC C X), IsAdmissible C x₀ U → y ∈ U.toSubgroup := by
  rw [kernel, Subgroup.mem_iInf]
  exact ⟨fun h U hU ↦ h ⟨U, hU⟩, fun h U ↦ h U.1 U.2⟩

/-- The kernel is a normal subgroup. -/
instance kernel_normal : (kernel C x₀).Normal :=
  Subgroup.normal_iInf_normal fun U ↦ U.1.isNormal'

/-- The kernel is closed, so its quotient is profinite. -/
instance isClosed_kernel :
    IsClosed ((kernel C x₀ : Subgroup (freeProC C X)) : Set (freeProC C X)) := by
  rw [kernel, Subgroup.coe_iInf]
  exact isClosed_iInter fun U ↦ U.1.toOpenSubgroup.isClosed

/-- **Compactness for the admissible subgroups.** An open subgroup of the free pro-`C` group on
the type `X` containing the kernel contains an admissible open normal subgroup. -/
private theorem exists_isAdmissible_le {M : Subgroup (freeProC C X)}
    (hM : IsOpen (M : Set (freeProC C X))) (hKM : kernel C x₀ ≤ M) :
    ∃ U : OpenNormalSubgroup (freeProC C X), IsAdmissible C x₀ U ∧ U.toSubgroup ≤ M := by
  have : Nonempty {U : OpenNormalSubgroup (freeProC C X) // IsAdmissible C x₀ U} :=
    ⟨⟨_, isAdmissible_top C x₀⟩⟩
  obtain ⟨U, hU⟩ := Subgroup.exists_le_of_iInf_le_of_directed
    (U := fun U : {U : OpenNormalSubgroup (freeProC C X) // IsAdmissible C x₀ U} ↦ U.1.toSubgroup)
    (fun U ↦ U.1.toOpenSubgroup.isClosed)
    (fun U V ↦ ⟨⟨U.1 ⊓ V.1, U.2.inf V.2⟩, inf_le_left, inf_le_right⟩) hM hKM
  exact ⟨U.1, U.2, hU⟩

end freeProCPointed

/-- **The free pro-`C` group on the pointed topological space `(X, x₀)`**, the quotient of the
free pro-`C` group on the type `X` by the intersection of the admissible open normal subgroups.
What pins it down is its universal property `freeProCPointed.existsUnique_lift`: continuous maps
from `X` to a profinite pro-`C` group sending `x₀` to `1` correspond to continuous homomorphisms
out of it. For a profinite space `X` this is `F_C(X, x₀)` of Ribes and Zalesskii, §3.3. -/
abbrev freeProCPointed : Type u :=
  freeProC C X ⧸ freeProCPointed.kernel C x₀

/-- The free pro-`C` group on a pointed space is pro-`C`. -/
theorem isProC_freeProCPointed : IsProC C (freeProCPointed C x₀) :=
  (isProC_freeProC C X).quotient _

namespace freeProCPointed

/-- The canonical continuous quotient map from the free pro-`C` group on the type `X` to the free
pro-`C` group on the pointed space `(X, x₀)`. -/
noncomputable def mk : freeProC C X →ₜ* freeProCPointed C x₀ :=
  ContinuousMonoidHom.quotientMk (kernel C x₀)

/-- The canonical quotient map sends an element to its class. -/
theorem mk_apply (y : freeProC C X) : mk C x₀ y = (y : freeProCPointed C x₀) :=
  (rfl)

/-- The canonical quotient map, as a monoid homomorphism, is the quotient projection. -/
@[simp]
theorem coe_mk :
    (mk C x₀ : freeProC C X →* freeProCPointed C x₀) = QuotientGroup.mk' (kernel C x₀) :=
  (rfl)

/-- The canonical quotient map is surjective. -/
theorem mk_surjective : Function.Surjective (mk C x₀) :=
  QuotientGroup.mk'_surjective _

/-- The canonical map from the pointed space to its free pro-`C` group. -/
noncomputable def of (x : X) : freeProCPointed C x₀ :=
  mk C x₀ (freeProC.of x)

/-- The canonical quotient map sends a generator of the free pro-`C` group on the type `X` to the
image of the corresponding point. -/
@[simp]
theorem mk_of (x : X) : mk C x₀ (freeProC.of x) = of C x₀ x :=
  (rfl)

/-- The class of a generator of the free pro-`C` group on the type `X` is the image of the
corresponding point. -/
@[simp]
theorem coe_freeProC_of (x : X) :
    ((freeProC.of x : freeProC C X) : freeProCPointed C x₀) = of C x₀ x :=
  (rfl)

/-- The canonical map kills the base point. -/
@[simp]
theorem of_basePoint : of C x₀ x₀ = 1 :=
  (QuotientGroup.eq_one_iff _).mpr ((mem_kernel_iff C x₀).mpr fun _ hU ↦ hU.2)

/-- **The canonical map from the pointed space to its free pro-`C` group is continuous.** -/
theorem continuous_of : Continuous (of C x₀) := by
  rw [continuous_iff_forall_continuous_mk]
  intro W
  -- The preimage of `W` in the free pro-`C` group is open and contains the kernel, hence it
  -- contains an admissible `U₀`.
  have hMopen : IsOpen ((W.toSubgroup.comap (mk C x₀ : freeProC C X →* _) : Subgroup _) :
      Set (freeProC C X)) := by
    rw [Subgroup.coe_comap]
    exact W.toOpenSubgroup.isOpen.preimage (mk C x₀).continuous
  have hKM : kernel C x₀ ≤ W.toSubgroup.comap (mk C x₀ : freeProC C X →* _) :=
    fun y hy ↦ Subgroup.mem_comap.mpr (by
      rw [coe_mk, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff y).mpr hy]
      exact one_mem _)
  obtain ⟨U₀, hU₀, hle⟩ := exists_isAdmissible_le C x₀ hMopen hKM
  -- The map to the quotient by `W` factors through the discrete quotient by `U₀`.
  have hfac : (fun x : X ↦ ((of C x₀ x : freeProCPointed C x₀) : _ ⧸ W.toSubgroup)) =
      QuotientGroup.map U₀.toSubgroup W.toSubgroup (mk C x₀ : freeProC C X →* _) hle ∘
        fun x : X ↦ ((freeProC.of x : freeProC C X) : freeProC C X ⧸ U₀.toSubgroup) := by
    funext x
    rw [Function.comp_apply, QuotientGroup.map_mk, coe_mk, QuotientGroup.mk'_apply,
      coe_freeProC_of]
  rw [hfac]
  exact continuous_of_discreteTopology.comp hU₀.1

/-- The image of the space generates its free pro-`C` group topologically. -/
theorem dense_closure_range_of :
    Dense ((Subgroup.closure (Set.range (of C x₀)) : Subgroup (freeProCPointed C x₀)) :
      Set (freeProCPointed C x₀)) := by
  have h := topologicalClosure_closure_image_eq_top
    (freeProC.topologicalClosure_closure_range_of_eq_top C X)
    (f := (mk C x₀ : freeProC C X →* freeProCPointed C x₀)) (map_continuous (mk C x₀))
    (mk_surjective C x₀).denseRange
  rw [← Set.range_comp, ← SetLike.coe_set_eq, Subgroup.topologicalClosure_coe, Subgroup.coe_top,
    ← dense_iff_closure_eq] at h
  exact h

section HomExt

variable {C x₀} {Q : Type v} [Group Q] [TopologicalSpace Q] [T2Space Q]

/-- Two continuous homomorphisms out of the free pro-`C` group on a pointed space that agree on
the image of the space are equal. -/
@[ext]
theorem hom_ext {φ ψ : freeProCPointed C x₀ →ₜ* Q} (h : ∀ x : X, φ (of C x₀ x) = ψ (of C x₀ x)) :
    φ = ψ := by
  apply ContinuousMonoidHom.ext
  intro q
  obtain ⟨y, rfl⟩ := mk_surjective C x₀ q
  have hcomp : φ.comp (mk C x₀) = ψ.comp (mk C x₀) :=
    freeProC.hom_ext fun x ↦ by simpa using h x
  exact DFunLike.congr_fun hcomp y

end HomExt

section Lift

variable {C x₀} {P : Type u} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]

/-- The preimage of an open normal subgroup of a profinite pro-`C` group under the lift of a
continuous base-point-preserving map is admissible. -/
private theorem isAdmissible_comap_lift (hP : IsProC C P) {f : X → P} (hf : Continuous f)
    (hf₀ : f x₀ = 1) (V : OpenNormalSubgroup P) :
    IsAdmissible C x₀ (V.comap (freeProC.lift hP f : freeProC C X →* P)
      (freeProC.lift hP f).continuous) := by
  have hcomp : (freeProC.lift hP f : freeProC C X →* P) ∘ (freeProC.of : X → freeProC C X) = f :=
    funext fun x ↦ freeProC.lift_of hP f x
  refine ⟨OpenNormalSubgroup.continuous_mk_comap V _ _ (by rw [hcomp]; exact hf), ?_⟩
  refine OpenNormalSubgroup.mem_comap.mpr ?_
  rw [MonoidHom.coe_coe, freeProC.lift_of, hf₀]
  exact one_mem _

/-- The kernel dies under the lift of a continuous base-point-preserving map to a profinite pro-`C`
group. -/
private theorem kernel_le_ker_lift (hP : IsProC C P) {f : X → P} (hf : Continuous f)
    (hf₀ : f x₀ = 1) : kernel C x₀ ≤ (freeProC.lift hP f : freeProC C X →* P).ker := by
  intro y hy
  rw [MonoidHom.mem_ker]
  have h : freeProC.lift hP f y ∈ ⨅ V : OpenNormalSubgroup P, V.toSubgroup :=
    Subgroup.mem_iInf.mpr fun V ↦ OpenNormalSubgroup.mem_comap.mp
      ((mem_kernel_iff C x₀).mp hy _ (isAdmissible_comap_lift hP hf hf₀ V))
  rwa [Subgroup.iInf_openNormalSubgroup_eq_bot, Subgroup.mem_bot] at h

/-- The continuous homomorphism from the free pro-`C` group on a pointed space to a profinite
pro-`C` group extending a continuous map that kills the base point. -/
noncomputable def lift (hP : IsProC C P) (f : X → P) (hf : Continuous f) (hf₀ : f x₀ = 1) :
    freeProCPointed C x₀ →ₜ* P :=
  ContinuousMonoidHom.quotientLift (kernel C x₀) (freeProC.lift hP f) (kernel_le_ker_lift hP hf hf₀)

/-- The lift recovers the free pro-`C` lift along the quotient map. -/
@[simp]
theorem lift_comp_mk (hP : IsProC C P) (f : X → P) (hf : Continuous f) (hf₀ : f x₀ = 1) :
    (lift hP f hf hf₀).comp (mk C x₀) = freeProC.lift hP f :=
  ContinuousMonoidHom.quotientLift_comp_quotientMk _ _ _

/-- The lift evaluates on classes as the free pro-`C` lift. -/
@[simp]
theorem lift_mk (hP : IsProC C P) (f : X → P) (hf : Continuous f) (hf₀ : f x₀ = 1)
    (y : freeProC C X) : lift hP f hf hf₀ (mk C x₀ y) = freeProC.lift hP f y :=
  DFunLike.congr_fun (lift_comp_mk hP f hf hf₀) y

/-- The lift of `f` agrees with `f` on the image of the space. -/
@[simp]
theorem lift_of (hP : IsProC C P) (f : X → P) (hf : Continuous f) (hf₀ : f x₀ = 1) (x : X) :
    lift hP f hf hf₀ (of C x₀ x) = f x := by
  rw [← mk_of, lift_mk, freeProC.lift_of]

/-- A continuous homomorphism restricting to `f` on the image of the space is the lift of `f`. -/
theorem lift_unique (hP : IsProC C P) (f : X → P) (hf : Continuous f) (hf₀ : f x₀ = 1)
    (g : freeProCPointed C x₀ →ₜ* P) (hg : ∀ x : X, g (of C x₀ x) = f x) : g = lift hP f hf hf₀ :=
  hom_ext fun x ↦ by rw [hg, lift_of]

/-- **The universal property of the free pro-`C` group on a pointed space.** Every continuous map
from `X` to a profinite pro-`C` group that sends `x₀` to `1` extends uniquely to a continuous
homomorphism from `freeProCPointed C x₀`. -/
theorem existsUnique_lift (hP : IsProC C P) (f : X → P) (hf : Continuous f) (hf₀ : f x₀ = 1) :
    ∃! g : freeProCPointed C x₀ →ₜ* P, ∀ x : X, g (of C x₀ x) = f x :=
  ⟨lift hP f hf hf₀, lift_of hP f hf hf₀, fun g hg ↦ lift_unique hP f hf hf₀ g hg⟩

/-- The lift is natural in its target. -/
@[simp]
theorem comp_lift {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [TotallyDisconnectedSpace Q] (hP : IsProC C P) (hQ : IsProC C Q)
    (g : P →ₜ* Q) (f : X → P) (hf : Continuous f) (hf₀ : f x₀ = 1) :
    g.comp (lift hP f hf hf₀) =
      lift hQ (⇑g ∘ f) (g.continuous.comp hf) (by rw [Function.comp_apply, hf₀, map_one]) :=
  hom_ext fun x ↦ by simp

/-- A continuous base-point-preserving map whose range generates the target topologically lifts
to a surjection. -/
theorem lift_surjective (hP : IsProC C P) {f : X → P} (hf : Continuous f) (hf₀ : f x₀ = 1)
    (hgen : Dense ((Subgroup.closure (Set.range f) : Subgroup P) : Set P)) :
    Function.Surjective (lift hP f hf hf₀) := by
  intro z
  obtain ⟨y, rfl⟩ := freeProC.lift_surjective hP hgen z
  exact ⟨mk C x₀ y, lift_mk hP f hf hf₀ y⟩

end Lift

/-! ### Discrete spaces -/

section Discrete

variable [DiscreteTopology X]

open scoped Classical in
/-- **For a discrete space, the free pro-`C` group on `(X, x₀)` is the free pro-`C` group on the
type `X ∖ {x₀}`**, matching the image of a point other than the base point with the corresponding
generator. -/
noncomputable def equivFreeProC : freeProCPointed C x₀ ≃ₜ* freeProC C {x : X // x ≠ x₀} where
  toFun := lift (isProC_freeProC C _) (fun x ↦ if h : x = x₀ then 1 else freeProC.of ⟨x, h⟩)
    continuous_of_discreteTopology (by simp)
  invFun := freeProC.lift (isProC_freeProCPointed C x₀) fun y ↦ of C x₀ y.1
  left_inv y := by
    have h : (freeProC.lift (isProC_freeProCPointed C x₀)
          fun y : {x : X // x ≠ x₀} ↦ of C x₀ y.1).comp
        (lift (isProC_freeProC C _) (fun x ↦ if h : x = x₀ then 1 else freeProC.of ⟨x, h⟩)
          continuous_of_discreteTopology (by simp)) =
        ContinuousMonoidHom.id (freeProCPointed C x₀) :=
      hom_ext fun x ↦ by
        by_cases hx : x = x₀
        · subst hx
          simp
        · simp [hx]
    exact DFunLike.congr_fun h y
  right_inv y := by
    have h : (lift (isProC_freeProC C _) (fun x ↦ if h : x = x₀ then 1 else freeProC.of ⟨x, h⟩)
        continuous_of_discreteTopology (by simp)).comp
          (freeProC.lift (isProC_freeProCPointed C x₀) fun y : {x : X // x ≠ x₀} ↦ of C x₀ y.1) =
        ContinuousMonoidHom.id (freeProC C {x : X // x ≠ x₀}) :=
      freeProC.hom_ext fun y ↦ by simp [y.2]
    exact DFunLike.congr_fun h y
  map_mul' := map_mul _
  continuous_toFun := map_continuous _
  continuous_invFun := map_continuous _

/-- The inverse of the identification with the free pro-`C` group on `X ∖ {x₀}` is the free
pro-`C` lift of the canonical map. -/
theorem equivFreeProC_symm_apply (y : freeProC C {x : X // x ≠ x₀}) :
    (equivFreeProC C x₀).symm y =
      freeProC.lift (isProC_freeProCPointed C x₀) (fun y : {x : X // x ≠ x₀} ↦ of C x₀ y.1) y :=
  (rfl)

/-- The inverse of the identification with the free pro-`C` group on `X ∖ {x₀}` sends a generator
to the image of the corresponding point. -/
@[simp]
theorem equivFreeProC_symm_of (y : {x : X // x ≠ x₀}) :
    (equivFreeProC C x₀).symm (freeProC.of y) = of C x₀ y.1 := by
  rw [equivFreeProC_symm_apply, freeProC.lift_of]

/-- The identification with the free pro-`C` group on `X ∖ {x₀}` sends the image of a point other
than the base point to the corresponding generator. -/
@[simp]
theorem equivFreeProC_of {x : X} (hx : x ≠ x₀) :
    equivFreeProC C x₀ (of C x₀ x) = freeProC.of ⟨x, hx⟩ :=
  ((equivFreeProC C x₀).symm_apply_eq.mp (equivFreeProC_symm_of C x₀ ⟨x, hx⟩)).symm

end Discrete

end freeProCPointed

end Admissible

/-! ### The one-point compactification -/

namespace freeProCPointed

open OnePoint

variable (C : FiniteGroupClass.{w}) (S : Type u) [TopologicalSpace S]

/-- The continuous homomorphism from the free pro-`C` group on the type `S` to the free pro-`C`
group on the one-point compactification `S⁺` pointed at `∞`, induced by the inclusion `S → S⁺`. -/
noncomputable def fromFreeProC : freeProC C S →ₜ* freeProCPointed C (∞ : OnePoint S) :=
  freeProC.lift (isProC_freeProCPointed C ∞) fun s ↦ of C ∞ (s : OnePoint S)

/-- The map from the free pro-`C` group on `S` sends a generator to the image of the corresponding
point of the one-point compactification. -/
@[simp]
theorem fromFreeProC_of (s : S) : fromFreeProC C S (freeProC.of s) = of C ∞ (s : OnePoint S) :=
  freeProC.lift_of _ _ _

/-- **The free pro-`C` group on `S` maps onto the free pro-`C` group on `(S⁺, ∞)`.** -/
theorem fromFreeProC_surjective : Function.Surjective (fromFreeProC C S) := by
  refine freeProC.lift_surjective _ ?_
  refine (dense_closure_range_of C (∞ : OnePoint S)).mono (SetLike.coe_subset_coe.mpr ?_)
  refine (Subgroup.closure_le _).mpr (Set.range_subset_iff.mpr fun x ↦ ?_)
  induction x using OnePoint.rec with
  | infty => rw [of_basePoint]; exact one_mem _
  | coe s => exact Subgroup.subset_closure ⟨s, rfl⟩

/-- **The images of the points of a discrete space converge to `1`** in the free pro-`C` group on
its pointed one-point compactification: the map `s ↦ of C ∞ s` tends to `1` along the cofinite
filter on `S`, that is every neighbourhood of `1` contains the images of all but finitely many
points of `S`. -/
theorem tendsto_of_coe_cofinite_nhds_one [DiscreteTopology S] :
    Filter.Tendsto (fun s : S ↦ of C ∞ (s : OnePoint S)) Filter.cofinite (nhds 1) := by
  have h := (continuous_iff_from_discrete (of C ∞)).mp (continuous_of C (∞ : OnePoint S))
  rwa [of_basePoint] at h

/-- The set of images of the points of a discrete space converges to one in the free pro-`C`
group on its pointed one-point compactification, in the sense of `TauCeti.ConvergesToOne`. -/
theorem convergesToOne_range_of_coe [DiscreteTopology S] :
    ConvergesToOne (Set.range fun s : S ↦ of C ∞ (s : OnePoint S)) :=
  (tendsto_of_coe_cofinite_nhds_one C S).convergesToOne_range

end freeProCPointed

end TauCeti
