/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.ProC

/-!
# Free pro-`C` and free pro-`p` groups on a type

For a class `C` of finite groups, the free pro-`C` group on `X` is the pro-`C` completion of
the free profinite group on `X`. The free pro-`p` group is defined directly as the maximal
pro-`p` quotient of that free profinite group. The comparison between the pro-`C` completion
for the class of finite `p`-groups and the maximal pro-`p` quotient identifies the two
constructions.

Both constructions are characterized by the expected universal property: an arbitrary map from
`X` to a profinite group of the relevant class extends uniquely to a continuous homomorphism.
The file also records functoriality in `X` and the fact that a surjection of generating types
induces a surjection of free groups.

## Main definitions

* `TauCeti.freeProC`: the free pro-`C` group on a type.
* `TauCeti.freeProP`: the free pro-`p` group on a type.
* `TauCeti.freeProC.of`, `TauCeti.freeProP.of`: their canonical generators.
* `TauCeti.freeProC.lift`, `TauCeti.freeProP.lift`: extension from the generators.
* `TauCeti.freeProC.map`, `TauCeti.freeProP.map`: functoriality in the generating type.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Chapter 3.
-/

public section

namespace TauCeti

universe u v

/-! ## Free pro-`C` groups -/

/-- The **free pro-`C` group** on `X`, obtained by taking the pro-`C` completion of the free
profinite group on `X`. -/
noncomputable abbrev freeProC (C : FiniteGroupClass.{u}) (X : Type u) : Type u :=
  proCCompletion C (freeProfiniteGroup X)

/-- A free pro-`C` group is pro-`C`. -/
theorem isProC_freeProC (C : FiniteGroupClass.{u}) (X : Type u) : IsProC C (freeProC C X) :=
  isProC_proCCompletion

namespace freeProC

variable {C : FiniteGroupClass.{u}} {X Y Z : Type u}

/-- The canonical continuous quotient map from the free profinite group to the free pro-`C`
group. -/
noncomputable def fromFreeProfiniteGroup (C : FiniteGroupClass.{u}) (X : Type u) :
    freeProfiniteGroup X →ₜ* freeProC C X :=
  ⟨proCCompletion.mk C (freeProfiniteGroup X), proCCompletion.continuous_mk C _⟩

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

/-- The lift of `f` agrees with `f` on every canonical generator. -/
@[simp]
theorem lift_of (hP : IsProC C P) (f : X → P) (x : X) : lift hP f (of x) = f x := by
  exact (proCCompletion.lift_mk hP (freeProfiniteGroup.lift f).toMonoidHom
    (freeProfiniteGroup.lift f).continuous (freeProfiniteGroup.of x)).trans
      (freeProfiniteGroup.lift_of f x)

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

end Lift

section Map

/-- The continuous homomorphism of free pro-`C` groups induced by a map of generating types. -/
noncomputable def map (f : X → Y) : freeProC C X →ₜ* freeProC C Y :=
  lift (isProC_freeProC C Y) (of ∘ f)

/-- `map f` carries the generator at `x` to the generator at `f x`. -/
@[simp]
theorem map_of (f : X → Y) (x : X) : map (C := C) f (of x) = of (f x) :=
  lift_of _ _ _

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

/-- A surjection of generating types induces a surjection of free pro-`C` groups. -/
theorem map_surjective {f : X → Y} (hf : Function.Surjective f) :
    Function.Surjective (map (C := C) f) := by
  intro y
  obtain ⟨y, rfl⟩ := fromFreeProfiniteGroup_surjective (C := C) (X := Y) y
  obtain ⟨x, rfl⟩ := freeProfiniteGroup.map_surjective hf y
  refine ⟨fromFreeProfiniteGroup C X x, ?_⟩
  exact DFunLike.congr_fun (map_comp_fromFreeProfiniteGroup (C := C) f) x

end Map

end freeProC

/-! ## Free pro-`p` groups -/

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
noncomputable def fromFreeProfiniteGroup (p : ℕ) (X : Type u) :
    freeProfiniteGroup X →ₜ* freeProP p X :=
  ⟨maximalProPQuotient.mk p (freeProfiniteGroup X), maximalProPQuotient.continuous_mk p _⟩

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

/-- The lift of `f` agrees with `f` on every canonical generator. -/
@[simp]
theorem lift_of (hP : IsProP p P) (f : X → P) (x : X) : lift hP f (of x) = f x := by
  exact (maximalProPQuotient.lift_mk hP (freeProfiniteGroup.lift f).toMonoidHom
    (freeProfiniteGroup.lift f).continuous (freeProfiniteGroup.of x)).trans
      (freeProfiniteGroup.lift_of f x)

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

end Lift

section Map

/-- The continuous homomorphism of free pro-`p` groups induced by a map of generating types. -/
noncomputable def map (f : X → Y) : freeProP p X →ₜ* freeProP p Y :=
  lift (isProP_freeProP p Y) (of ∘ f)

/-- `map f` carries the generator at `x` to the generator at `f x`. -/
@[simp]
theorem map_of (f : X → Y) (x : X) : map (p := p) f (of x) = of (f x) :=
  lift_of _ _ _

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

/-- A surjection of generating types induces a surjection of free pro-`p` groups. -/
theorem map_surjective {f : X → Y} (hf : Function.Surjective f) :
    Function.Surjective (map (p := p) f) := by
  intro y
  obtain ⟨y, rfl⟩ := fromFreeProfiniteGroup_surjective (p := p) (X := Y) y
  obtain ⟨x, rfl⟩ := freeProfiniteGroup.map_surjective hf y
  refine ⟨fromFreeProfiniteGroup p X x, ?_⟩
  exact DFunLike.congr_fun (map_comp_fromFreeProfiniteGroup (p := p) f) x

end Map

end freeProP

/-! ## Comparison -/

namespace freeProC

/-- For the class of finite `p`-groups, the free pro-`C` group is canonically isomorphic to the
free pro-`p` group. -/
noncomputable def equivFreeProP (p : ℕ) (X : Type u) :
    freeProC (finiteGroupClassP.{u} p) X ≃ₜ* freeProP p X :=
  proCCompletion.equivMaximalProPQuotient p (freeProfiniteGroup X)

/-- The comparison with the free pro-`p` group preserves each canonical generator. -/
@[simp]
theorem equivFreeProP_of (p : ℕ) (x : X) :
    equivFreeProP p X (of x) = freeProP.of x := by
  exact proCCompletion.equivMaximalProPQuotient_mk (p := p)
    (G := freeProfiniteGroup X) (freeProfiniteGroup.of x)

end freeProC

end TauCeti
