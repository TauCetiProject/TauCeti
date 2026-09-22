/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP

/-!
# Free pro-`p` groups on a type

The free pro-`p` group on `X` is defined directly as the maximal pro-`p` quotient of the free
profinite group on `X`. A map from `X` to a pro-`p` profinite group in the same universe extends
uniquely to a continuous homomorphism. Extensionality for homomorphisms out of the free pro-`p`
group only requires a Hausdorff group target, which may live in any universe.

The file also records functoriality in `X` and the fact that a surjection of generating types
induces a surjection of free pro-`p` groups.

## Main definitions

* `TauCeti.freeProP`: the free pro-`p` group on a type.
* `TauCeti.freeProP.of`: its canonical generators.
* `TauCeti.freeProP.lift`: extension from the generators.
* `TauCeti.freeProP.map`: functoriality in the generating type.

## Main results

* `TauCeti.isProP_freeProP`: a free pro-`p` group is pro-`p`.
* `TauCeti.freeProP.hom_ext`: homomorphisms agreeing on the generators are equal.
* `TauCeti.freeProP.existsUnique_lift`: the universal property.
* `TauCeti.freeProP.lift_surjective`: a topologically generating map lifts to a surjection.
* `TauCeti.freeProP.map_surjective`: a surjection of generating types induces a surjection.
* `TauCeti.freeProP.existsUnique_continuousMulEquiv`: the free pro-`p` group is unique up to a
  unique topological isomorphism matching the generators.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Chapter 3.
-/

public section

namespace TauCeti

universe u v

/-- The **free pro-`p` group** on `X`, obtained directly as the maximal pro-`p` quotient of the
free profinite group on `X`. -/
noncomputable abbrev freeProP (p : ℕ) (X : Type u) : Type u :=
  maximalProPQuotient p (freeProfiniteGroup X)

/-- A free pro-`p` group is pro-`p`. -/
theorem isProP_freeProP (p : ℕ) (X : Type u) : IsProP p (freeProP p X) :=
  isProP_maximalProPQuotient

namespace freeProP

variable {p : ℕ} {X Y Z : Type u}

/-- The canonical continuous quotient map from the free profinite group to the free pro-`p`
group. -/
@[expose] noncomputable def fromFreeProfiniteGroup (p : ℕ) (X : Type u) :
    freeProfiniteGroup X →ₜ* freeProP p X :=
  ⟨maximalProPQuotient.mk p (freeProfiniteGroup X), maximalProPQuotient.continuous_mk p _⟩

/-- Evaluation of the canonical quotient map agrees with the underlying quotient homomorphism. -/
theorem fromFreeProfiniteGroup_apply (p : ℕ) (X : Type u) (x : freeProfiniteGroup X) :
    fromFreeProfiniteGroup p X x = maximalProPQuotient.mk p (freeProfiniteGroup X) x :=
  rfl

/-- The canonical map from the generating type into the free pro-`p` group. -/
noncomputable def of (x : X) : freeProP p X :=
  fromFreeProfiniteGroup p X (freeProfiniteGroup.of x)

/-- The canonical quotient map sends a free profinite generator to the corresponding free
pro-`p` generator. -/
@[simp]
theorem fromFreeProfiniteGroup_of (x : X) :
    fromFreeProfiniteGroup p X (freeProfiniteGroup.of x) = of x :=
  (rfl)

/-- The canonical map from the free profinite group to the free pro-`p` group is surjective. -/
theorem fromFreeProfiniteGroup_surjective :
    Function.Surjective (fromFreeProfiniteGroup p X) :=
  maximalProPQuotient.mk_surjective p (freeProfiniteGroup X)

section HomExt

variable {Q : Type v} [Group Q] [TopologicalSpace Q] [T2Space Q]

/-- Two continuous homomorphisms out of a free pro-`p` group that agree on the generators are
equal. -/
@[ext]
theorem hom_ext {f g : freeProP p X →ₜ* Q} (h : ∀ x : X, f (of x) = g (of x)) : f = g := by
  apply ContinuousMonoidHom.ext
  intro y
  obtain ⟨y, rfl⟩ := fromFreeProfiniteGroup_surjective (p := p) (X := X) y
  have hcomp : f.comp (fromFreeProfiniteGroup p X) =
      g.comp (fromFreeProfiniteGroup p X) :=
    freeProfiniteGroup.hom_ext fun x ↦ by simpa using h x
  exact DFunLike.congr_fun hcomp y

end HomExt

section Lift

variable {P : Type u} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]

/-- The continuous homomorphism from a free pro-`p` group extending a map on its generators. -/
noncomputable def lift (hP : IsProP p P) (f : X → P) : freeProP p X →ₜ* P :=
  ⟨maximalProPQuotient.lift hP (freeProfiniteGroup.lift f).toMonoidHom
      (freeProfiniteGroup.lift f).continuous,
    maximalProPQuotient.continuous_lift hP (freeProfiniteGroup.lift f).toMonoidHom
      (freeProfiniteGroup.lift f).continuous⟩

/-- The free pro-`p` lift recovers the free profinite lift along the quotient map. -/
@[simp]
theorem lift_comp_fromFreeProfiniteGroup (hP : IsProP p P) (f : X → P) :
    (lift hP f).comp (fromFreeProfiniteGroup p X) = freeProfiniteGroup.lift f := by
  apply ContinuousMonoidHom.ext
  intro x
  exact maximalProPQuotient.lift_mk hP (freeProfiniteGroup.lift f).toMonoidHom
    (freeProfiniteGroup.lift f).continuous x

/-- The free pro-`p` lift evaluates on the image of the free profinite group as the free
profinite lift. -/
@[simp]
theorem lift_fromFreeProfiniteGroup (hP : IsProP p P) (f : X → P)
    (x : freeProfiniteGroup X) :
    lift hP f (fromFreeProfiniteGroup p X x) = freeProfiniteGroup.lift f x :=
  DFunLike.congr_fun (lift_comp_fromFreeProfiniteGroup hP f) x

/-- The lift of `f` agrees with `f` on every canonical generator. -/
@[simp]
theorem lift_of (hP : IsProP p P) (f : X → P) (x : X) : lift hP f (of x) = f x := by
  rw [← fromFreeProfiniteGroup_of, lift_fromFreeProfiniteGroup,
    freeProfiniteGroup.lift_of]

/-- A continuous homomorphism restricting to `f` on the generators is the canonical lift of
`f`. -/
theorem lift_unique (hP : IsProP p P) (f : X → P) (g : freeProP p X →ₜ* P)
    (hg : ∀ x : X, g (of x) = f x) : g = lift hP f :=
  hom_ext fun x ↦ by rw [hg, lift_of]

/-- **The universal property of the free pro-`p` group.** Every map from `X` to a profinite
pro-`p` group extends uniquely to a continuous homomorphism from `freeProP p X`. -/
theorem existsUnique_lift (hP : IsProP p P) (f : X → P) :
    ∃! g : freeProP p X →ₜ* P, ∀ x : X, g (of x) = f x :=
  ⟨lift hP f, lift_of hP f, fun g hg ↦ lift_unique hP f g hg⟩

/-- The free pro-`p` lift is natural in its target. -/
@[simp]
theorem comp_lift {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [TotallyDisconnectedSpace Q] (hP : IsProP p P) (hQ : IsProP p Q)
    (g : P →ₜ* Q) (f : X → P) : g.comp (lift hP f) = lift hQ (⇑g ∘ f) :=
  hom_ext fun x ↦ by simp

/-- A map whose range generates the target topologically lifts to a surjection. -/
theorem lift_surjective (hP : IsProP p P) {f : X → P}
    (hf : Dense ((Subgroup.closure (Set.range f) : Subgroup P) : Set P)) :
    Function.Surjective (lift hP f) := by
  intro y
  obtain ⟨x, rfl⟩ := freeProfiniteGroup.lift_surjective hf y
  exact ⟨fromFreeProfiniteGroup p X x, lift_fromFreeProfiniteGroup hP f x⟩

end Lift

section Map

/-- The continuous homomorphism of free pro-`p` groups induced by a map of generating types. -/
noncomputable def map (f : X → Y) : freeProP p X →ₜ* freeProP p Y :=
  lift (isProP_freeProP p Y) (of ∘ f)

/-- `map f` carries the generator at `x` to the generator at `f x`. -/
@[simp]
theorem map_of (f : X → Y) (x : X) : map (p := p) f (of x) = of (f x) :=
  lift_of _ _ _

/-- The free pro-`p` lift is natural in the generating type. -/
@[simp]
theorem lift_comp_map {P : Type u} [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
    [CompactSpace P] [TotallyDisconnectedSpace P] (hP : IsProP p P) (f : Y → P)
    (g : X → Y) : (lift hP f).comp (map (p := p) g) = lift hP (f ∘ g) :=
  hom_ext fun x ↦ by simp

/-- Mapping the generating type by the identity induces the identity homomorphism. -/
@[simp]
theorem map_id : map (p := p) (id : X → X) = ContinuousMonoidHom.id (freeProP p X) :=
  hom_ext fun x ↦ by simp

/-- The maps induced by maps of generating types compose functorially. -/
@[simp]
theorem map_comp (f : X → Y) (g : Y → Z) :
    map (p := p) (g ∘ f) = (map g).comp (map f) :=
  (hom_ext fun x ↦ by simp).symm

/-- The map induced on free pro-`p` groups commutes with the canonical maps from the free
profinite groups. -/
@[simp]
theorem map_comp_fromFreeProfiniteGroup (f : X → Y) :
    (map (p := p) f).comp (fromFreeProfiniteGroup p X) =
      (fromFreeProfiniteGroup p Y).comp (freeProfiniteGroup.map f) :=
  freeProfiniteGroup.hom_ext fun x ↦ by simp

/-- The map induced on free pro-`p` groups evaluates compatibly with the map induced on free
profinite groups. -/
@[simp]
theorem map_fromFreeProfiniteGroup (f : X → Y) (x : freeProfiniteGroup X) :
    map (p := p) f (fromFreeProfiniteGroup p X x) =
      fromFreeProfiniteGroup p Y (freeProfiniteGroup.map f x) :=
  DFunLike.congr_fun (map_comp_fromFreeProfiniteGroup (p := p) f) x

/-- A surjection of generating types induces a surjection of free pro-`p` groups. -/
theorem map_surjective {f : X → Y} (hf : Function.Surjective f) :
    Function.Surjective (map (p := p) f) := by
  apply lift_surjective
  rw [hf.range_comp (of : Y → freeProP p Y)]
  apply (fromFreeProfiniteGroup_surjective (p := p) (X := Y)).denseRange.dense_of_mapsTo
    (map_continuous (fromFreeProfiniteGroup p Y))
    (freeProfiniteGroup.dense_closure_range_of Y)
  intro y hy
  have hle : Subgroup.closure (Set.range (freeProfiniteGroup.of : Y → freeProfiniteGroup Y)) ≤
      (Subgroup.closure (Set.range (of : Y → freeProP p Y))).comap
        (fromFreeProfiniteGroup p Y).toMonoidHom := by
    apply (Subgroup.closure_le _).2
    exact Set.range_subset_iff.mpr fun x ↦ by
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      -- `Subgroup.mem_comap` exposes the underlying monoid hom; align its coercion with the
      -- continuous hom before applying the public generator equation.
      change fromFreeProfiniteGroup p Y (freeProfiniteGroup.of x) ∈
        Subgroup.closure (Set.range (of : Y → freeProP p Y))
      rw [fromFreeProfiniteGroup_of]
      exact Subgroup.subset_closure ⟨x, rfl⟩
  exact hle hy

end Map

section Uniqueness

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G]

/-- **The free pro-`p` group is unique up to a unique isomorphism.** A pro-`p` group `G` with
a map `ι : X → G` through which every map from `X` to a pro-`p` profinite group factors
uniquely is topologically isomorphic to `freeProP p X` by a unique isomorphism matching the
two families of generators. -/
theorem existsUnique_continuousMulEquiv (hG : IsProP p G) (ι : X → G)
    (h : ∀ (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
      [TotallyDisconnectedSpace P] (_hP : IsProP p P) (f : X → P),
        ∃! φ : G →ₜ* P, ∀ x : X, φ (ι x) = f x) :
    ∃! e : freeProP p X ≃ₜ* G, ∀ x : X, e (of x) = ι x := by
  obtain ⟨ψ, hψ, -⟩ := h (freeProP p X) (isProP_freeProP p X) of
  have hleft : ψ.comp (lift hG ι) = ContinuousMonoidHom.id (freeProP p X) :=
    hom_ext fun x ↦ by simp [hψ x]
  have hright : (lift hG ι).comp ψ = ContinuousMonoidHom.id G :=
    (h G hG ι).unique (fun x ↦ by simp [hψ x]) (fun _ ↦ rfl)
  refine ⟨{ toFun := lift hG ι, invFun := ψ
            left_inv := fun a ↦ congrArg (fun φ : freeProP p X →ₜ* _ ↦ φ a) hleft
            right_inv := fun g ↦ congrArg (fun φ : G →ₜ* G ↦ φ g) hright
            map_mul' := map_mul (lift hG ι)
            continuous_toFun := map_continuous (lift hG ι)
            continuous_invFun := map_continuous ψ }, lift_of hG ι, fun e he ↦ ?_⟩
  have hcoe : (e : freeProP p X →ₜ* G) = lift hG ι := hom_ext fun x ↦ by simp [he x]
  exact ContinuousMulEquiv.ext fun a ↦ congrArg (fun φ : freeProP p X →ₜ* G ↦ φ a) hcoe

end Uniqueness

end freeProP

end TauCeti
