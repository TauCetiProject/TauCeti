/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProP
public import TauCeti.Topology.Algebra.Group.Profinite.ProC

/-!
# Free pro-`C` groups on a type

For a class `C` of finite groups, the free pro-`C` group on `X` is the pro-`C` completion of
the free profinite group on `X`. The comparison between the pro-`C` completion for the class
of finite `p`-groups and the directly constructed free pro-`p` group identifies the two
constructions.

The construction has the expected universal property: a map from `X` to a pro-`C` profinite
group in the same universe extends uniquely to a continuous homomorphism. Extensionality for
homomorphisms out of the free pro-`C` group only requires a Hausdorff group target, which may live
in any universe. The file also records functoriality in `X` and the fact that a surjection of
generating types induces a surjection of free groups.

## Main definitions

* `TauCeti.freeProC`: the free pro-`C` group on a type.
* `TauCeti.freeProC.of`: its canonical generators.
* `TauCeti.freeProC.lift`: extension from the generators.
* `TauCeti.freeProC.map`: functoriality in the generating type.
* `TauCeti.freeProC.equivFreeProP`: comparison with the directly constructed free pro-`p` group.

## Main results

* `TauCeti.isProC_freeProC`: a free pro-`C` group is pro-`C`.
* `TauCeti.freeProC.hom_ext`: homomorphisms agreeing on the generators are equal.
* `TauCeti.freeProC.existsUnique_lift`: the universal property.
* `TauCeti.freeProC.lift_surjective`: a topologically generating map lifts to a surjection.
* `TauCeti.freeProC.map_surjective`: a surjection of generating types induces a surjection.
* `TauCeti.freeProC.existsUnique_continuousMulEquiv`: the free pro-`C` group is unique up to a
  unique topological isomorphism matching the generators.
* `TauCeti.freeProC.equivFreeProP_of`: the comparison preserves the generators.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Chapter 3.
-/

public section

namespace TauCeti

universe u v w

/-! ## Free pro-`C` groups -/

/-- The **free pro-`C` group** on `X`, obtained by taking the pro-`C` completion of the free
profinite group on `X`. -/
noncomputable abbrev freeProC (C : FiniteGroupClass.{w}) (X : Type u) : Type u :=
  proCCompletion C (freeProfiniteGroup X)

/-- A free pro-`C` group is pro-`C`. -/
theorem isProC_freeProC (C : FiniteGroupClass.{w}) (X : Type u) : IsProC C (freeProC C X) :=
  isProC_proCCompletion

namespace freeProC

variable {C : FiniteGroupClass.{w}} {X Y Z : Type u}

/-- The canonical continuous quotient map from the free profinite group to the free pro-`C`
group. -/
noncomputable def fromFreeProfiniteGroup : (C : FiniteGroupClass.{w}) → (X : Type u) →
    freeProfiniteGroup X →ₜ* freeProC C X
  | C, X =>
    ⟨proCCompletion.mk C (freeProfiniteGroup X), proCCompletion.continuous_mk C _⟩

/-- Evaluation of the canonical quotient map agrees with the underlying quotient homomorphism. -/
@[simp low]
theorem fromFreeProfiniteGroup_apply (C : FiniteGroupClass.{w}) (X : Type u)
    (x : freeProfiniteGroup X) :
    fromFreeProfiniteGroup C X x = proCCompletion.mk C (freeProfiniteGroup X) x := by
  rw [fromFreeProfiniteGroup]
  rfl

/-- The canonical map from the generating type into the free pro-`C` group. -/
noncomputable def of (x : X) : freeProC C X :=
  fromFreeProfiniteGroup C X (freeProfiniteGroup.of x)

/-- The canonical quotient map sends a free profinite generator to the corresponding free
pro-`C` generator. -/
@[simp]
theorem fromFreeProfiniteGroup_of (x : X) :
    fromFreeProfiniteGroup C X (freeProfiniteGroup.of x) = of x :=
  (rfl)

/-- The canonical map from the free profinite group to the free pro-`C` group is surjective. -/
theorem fromFreeProfiniteGroup_surjective :
    Function.Surjective (fromFreeProfiniteGroup C X) :=
  proCCompletion.mk_surjective C (freeProfiniteGroup X)

section HomExt

variable {Q : Type v} [Group Q] [TopologicalSpace Q] [T2Space Q]

/-- Two continuous homomorphisms out of a free pro-`C` group that agree on the generators are
equal. -/
@[ext]
theorem hom_ext {f g : freeProC C X →ₜ* Q} (h : ∀ x : X, f (of x) = g (of x)) : f = g := by
  apply ContinuousMonoidHom.ext
  intro y
  obtain ⟨y, rfl⟩ := fromFreeProfiniteGroup_surjective (C := C) (X := X) y
  have hcomp : f.comp (fromFreeProfiniteGroup C X) =
      g.comp (fromFreeProfiniteGroup C X) :=
    freeProfiniteGroup.hom_ext fun x ↦ by simpa using h x
  exact DFunLike.congr_fun hcomp y

end HomExt

section Lift

variable {P : Type u} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]

/-- The continuous homomorphism from a free pro-`C` group extending a map on its generators. -/
noncomputable def lift (hP : IsProC C P) (f : X → P) : freeProC C X →ₜ* P :=
  ⟨proCCompletion.lift hP (freeProfiniteGroup.lift f).toMonoidHom
      (freeProfiniteGroup.lift f).continuous,
    proCCompletion.continuous_lift hP (freeProfiniteGroup.lift f).toMonoidHom
      (freeProfiniteGroup.lift f).continuous⟩

/-- The free pro-`C` lift recovers the free profinite lift along the quotient map. -/
@[simp]
theorem lift_comp_fromFreeProfiniteGroup (hP : IsProC C P) (f : X → P) :
    (lift hP f).comp (fromFreeProfiniteGroup C X) = freeProfiniteGroup.lift f := by
  apply ContinuousMonoidHom.ext
  intro x
  exact proCCompletion.lift_mk hP (freeProfiniteGroup.lift f).toMonoidHom
    (freeProfiniteGroup.lift f).continuous x

/-- The free pro-`C` lift evaluates on the image of the free profinite group as the free
profinite lift. -/
@[simp]
theorem lift_fromFreeProfiniteGroup (hP : IsProC C P) (f : X → P)
    (x : freeProfiniteGroup X) :
    lift hP f (fromFreeProfiniteGroup C X x) = freeProfiniteGroup.lift f x :=
  DFunLike.congr_fun (lift_comp_fromFreeProfiniteGroup hP f) x

/-- The lift of `f` agrees with `f` on every canonical generator. -/
@[simp]
theorem lift_of (hP : IsProC C P) (f : X → P) (x : X) : lift hP f (of x) = f x := by
  rw [← fromFreeProfiniteGroup_of, lift_fromFreeProfiniteGroup,
    freeProfiniteGroup.lift_of]

/-- A continuous homomorphism restricting to `f` on the generators is the canonical lift of
`f`. -/
theorem lift_unique (hP : IsProC C P) (f : X → P) (g : freeProC C X →ₜ* P)
    (hg : ∀ x : X, g (of x) = f x) : g = lift hP f :=
  hom_ext fun x ↦ by rw [hg, lift_of]

/-- **The universal property of the free pro-`C` group.** Every map from `X` to a profinite
pro-`C` group extends uniquely to a continuous homomorphism from `freeProC C X`. -/
theorem existsUnique_lift (hP : IsProC C P) (f : X → P) :
    ∃! g : freeProC C X →ₜ* P, ∀ x : X, g (of x) = f x :=
  ⟨lift hP f, lift_of hP f, fun g hg ↦ lift_unique hP f g hg⟩

/-- The free pro-`C` lift is natural in its target. -/
@[simp]
theorem comp_lift {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [TotallyDisconnectedSpace Q] (hP : IsProC C P) (hQ : IsProC C Q)
    (g : P →ₜ* Q) (f : X → P) : g.comp (lift hP f) = lift hQ (⇑g ∘ f) :=
  hom_ext fun x ↦ by simp

/-- A map whose range generates the target topologically lifts to a surjection. -/
theorem lift_surjective (hP : IsProC C P) {f : X → P}
    (hf : Dense ((Subgroup.closure (Set.range f) : Subgroup P) : Set P)) :
    Function.Surjective (lift hP f) := by
  intro y
  obtain ⟨x, rfl⟩ := freeProfiniteGroup.lift_surjective hf y
  exact ⟨fromFreeProfiniteGroup C X x, lift_fromFreeProfiniteGroup hP f x⟩

end Lift

section Map

/-- The continuous homomorphism of free pro-`C` groups induced by a map of generating types. -/
noncomputable def map (f : X → Y) : freeProC C X →ₜ* freeProC C Y :=
  lift (isProC_freeProC C Y) (of ∘ f)

/-- `map f` carries the generator at `x` to the generator at `f x`. -/
@[simp]
theorem map_of (f : X → Y) (x : X) : map (C := C) f (of x) = of (f x) :=
  lift_of _ _ _

/-- The free pro-`C` lift is natural in the generating type. -/
@[simp]
theorem lift_comp_map {P : Type u} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [TotallyDisconnectedSpace P] (hP : IsProC C P) (f : Y → P)
    (g : X → Y) : (lift hP f).comp (map (C := C) g) = lift hP (f ∘ g) :=
  hom_ext fun x ↦ by simp

/-- Mapping the generating type by the identity induces the identity homomorphism. -/
@[simp]
theorem map_id : map (C := C) (id : X → X) = ContinuousMonoidHom.id (freeProC C X) :=
  hom_ext fun x ↦ by simp

/-- The maps induced by maps of generating types compose functorially. -/
@[simp]
theorem map_comp (f : X → Y) (g : Y → Z) :
    map (C := C) (g ∘ f) = (map g).comp (map f) :=
  (hom_ext fun x ↦ by simp).symm

/-- The map induced on free pro-`C` groups commutes with the canonical maps from the free
profinite groups. -/
@[simp]
theorem map_comp_fromFreeProfiniteGroup (f : X → Y) :
    (map (C := C) f).comp (fromFreeProfiniteGroup C X) =
      (fromFreeProfiniteGroup C Y).comp (freeProfiniteGroup.map f) :=
  freeProfiniteGroup.hom_ext fun x ↦ by simp

/-- The map induced on free pro-`C` groups evaluates compatibly with the map induced on free
profinite groups. -/
@[simp]
theorem map_fromFreeProfiniteGroup (f : X → Y) (x : freeProfiniteGroup X) :
    map (C := C) f (fromFreeProfiniteGroup C X x) =
      fromFreeProfiniteGroup C Y (freeProfiniteGroup.map f x) :=
  DFunLike.congr_fun (map_comp_fromFreeProfiniteGroup (C := C) f) x

/-- A surjection of generating types induces a surjection of free pro-`C` groups. -/
theorem map_surjective {f : X → Y} (hf : Function.Surjective f) :
    Function.Surjective (map (C := C) f) := by
  apply lift_surjective
  rw [hf.range_comp (of : Y → freeProC C Y)]
  apply (fromFreeProfiniteGroup_surjective (C := C) (X := Y)).denseRange.dense_of_mapsTo
    (map_continuous (fromFreeProfiniteGroup C Y))
    (freeProfiniteGroup.dense_closure_range_of Y)
  intro y hy
  have hle : Subgroup.closure (Set.range (freeProfiniteGroup.of : Y → freeProfiniteGroup Y)) ≤
      (Subgroup.closure (Set.range (of : Y → freeProC C Y))).comap
        (fromFreeProfiniteGroup C Y).toMonoidHom := by
    apply (Subgroup.closure_le _).2
    exact Set.range_subset_iff.mpr fun x ↦ by
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      -- `Subgroup.mem_comap` exposes the underlying monoid hom; align its coercion with the
      -- continuous hom before applying the public generator equation.
      change fromFreeProfiniteGroup C Y (freeProfiniteGroup.of x) ∈
        Subgroup.closure (Set.range (of : Y → freeProC C Y))
      rw [fromFreeProfiniteGroup_of]
      exact Subgroup.subset_closure ⟨x, rfl⟩
  exact hle hy

end Map

section Uniqueness

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **The free pro-`C` group is unique up to a unique isomorphism.** A pro-`C` group `G` with
a map `ι : X → G` through which every map from `X` to a pro-`C` profinite group factors uniquely
is topologically isomorphic to `freeProC C X` by a unique isomorphism matching the two families
of generators. -/
theorem existsUnique_continuousMulEquiv (hG : IsProC C G) (ι : X → G)
    (h : ∀ (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
      [TotallyDisconnectedSpace P] (_hP : IsProC C P) (f : X → P),
        ∃! φ : G →ₜ* P, ∀ x : X, φ (ι x) = f x) :
    ∃! e : freeProC C X ≃ₜ* G, ∀ x : X, e (of x) = ι x := by
  obtain ⟨ψ, hψ, -⟩ := h (freeProC C X) (isProC_freeProC C X) of
  have hleft : ψ.comp (lift hG ι) = ContinuousMonoidHom.id (freeProC C X) :=
    hom_ext fun x ↦ by simp [hψ x]
  have hright : (lift hG ι).comp ψ = ContinuousMonoidHom.id G :=
    (h G hG ι).unique (fun x ↦ by simp [hψ x]) (fun _ ↦ rfl)
  refine ⟨{ toFun := lift hG ι, invFun := ψ
            left_inv := fun a ↦ congrArg (fun φ : freeProC C X →ₜ* _ ↦ φ a) hleft
            right_inv := fun g ↦ congrArg (fun φ : G →ₜ* G ↦ φ g) hright
            map_mul' := map_mul (lift hG ι)
            continuous_toFun := map_continuous (lift hG ι)
            continuous_invFun := map_continuous ψ }, lift_of hG ι, fun e he ↦ ?_⟩
  have hcoe : (e : freeProC C X →ₜ* G) = lift hG ι := hom_ext fun x ↦ by simp [he x]
  exact ContinuousMulEquiv.ext fun a ↦ congrArg (fun φ : freeProC C X →ₜ* G ↦ φ a) hcoe

end Uniqueness

end freeProC

/-! ## Comparison -/

namespace freeProC

/-- For the class of finite `p`-groups, the free pro-`C` group is canonically isomorphic to the
free pro-`p` group. -/
noncomputable def equivFreeProP (p : ℕ) (X : Type u) :
    freeProC (finiteGroupClassP.{u} p) X ≃ₜ* freeProP p X :=
  proCCompletion.equivMaximalProPQuotient p (freeProfiniteGroup X)

/-- The comparison with the free pro-`p` group commutes with the canonical quotient maps. -/
@[simp]
theorem equivFreeProP_fromFreeProfiniteGroup (p : ℕ) (X : Type u)
    (x : freeProfiniteGroup X) :
    equivFreeProP p X (fromFreeProfiniteGroup (finiteGroupClassP p) X x) =
      freeProP.fromFreeProfiniteGroup p X x := by
  rw [fromFreeProfiniteGroup_apply, freeProP.fromFreeProfiniteGroup_apply]
  exact proCCompletion.equivMaximalProPQuotient_mk (p := p)
    (G := freeProfiniteGroup X) x

/-- The comparison with the free pro-`p` group preserves each canonical generator. -/
@[simp]
theorem equivFreeProP_of (p : ℕ) (x : X) :
    equivFreeProP p X (of x) = freeProP.of x := by
  rw [← fromFreeProfiniteGroup_of, equivFreeProP_fromFreeProfiniteGroup,
    freeProP.fromFreeProfiniteGroup_of]

/-- The inverse comparison with the free pro-`p` group preserves each canonical generator. -/
@[simp]
theorem equivFreeProP_symm_of (p : ℕ) (x : X) :
    (equivFreeProP p X).symm (freeProP.of x) = of x := by
  apply (equivFreeProP p X).injective
  simp

/-- The comparison between the two free pro-`p` constructions is natural in the generators. -/
@[simp]
theorem equivFreeProP_comp_map (p : ℕ) (f : X → Y) :
    ((equivFreeProP p Y : freeProC (finiteGroupClassP.{u} p) Y ≃ₜ* freeProP p Y) :
        freeProC (finiteGroupClassP.{u} p) Y →ₜ* freeProP p Y).comp
          (map (C := finiteGroupClassP.{u} p) f) =
      (freeProP.map f).comp
        ((equivFreeProP p X : freeProC (finiteGroupClassP.{u} p) X ≃ₜ* freeProP p X) :
          freeProC (finiteGroupClassP.{u} p) X →ₜ* freeProP p X) :=
  hom_ext fun x ↦ by simp

/-- The comparison between the two free pro-`p` constructions evaluates naturally on maps of
generators. -/
@[simp]
theorem equivFreeProP_map (p : ℕ) (f : X → Y) (x : freeProC (finiteGroupClassP.{u} p) X) :
    equivFreeProP p Y (map (C := finiteGroupClassP.{u} p) f x) =
      freeProP.map f (equivFreeProP p X x) :=
  DFunLike.congr_fun (equivFreeProP_comp_map p f) x

/-- Lifting from either construction of a free pro-`p` group gives the same homomorphism. -/
@[simp]
theorem freeProP_lift_comp_equivFreeProP {P : Type u} [Group P] [TopologicalSpace P]
    [IsTopologicalGroup P] [CompactSpace P] [TotallyDisconnectedSpace P] (hP : IsProP p P)
    (f : X → P) :
    (freeProP.lift hP f).comp
        ((equivFreeProP p X : freeProC (finiteGroupClassP.{u} p) X ≃ₜ* freeProP p X) :
          freeProC (finiteGroupClassP.{u} p) X →ₜ* freeProP p X) =
      lift (isProC_finiteGroupClassP_iff.mpr hP) f :=
  hom_ext fun x ↦ by simp

end freeProC

end TauCeti
