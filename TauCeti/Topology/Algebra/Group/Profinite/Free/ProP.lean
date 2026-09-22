/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.Free.ProC

/-!
# Free pro-`p` groups on a type

The free pro-`p` group on `X` is defined directly as the maximal pro-`p` quotient of the free
profinite group on `X`. A map from `X` to a pro-`p` profinite group in the same universe extends
uniquely to a continuous homomorphism. Extensionality for homomorphisms out of the free pro-`p`
group only requires a Hausdorff group target, which may live in any universe.

The canonical comparison with the free pro-`C` group for the class of finite `p`-groups is used
to derive the universal property and functoriality. The file also records that a surjection of
generating types induces a surjection of free pro-`p` groups.

## Main definitions

* `TauCeti.freeProP`: the free pro-`p` group on a type.
* `TauCeti.freeProP.of`: its canonical generators.
* `TauCeti.freeProP.lift`: extension from the generators.
* `TauCeti.freeProP.map`: functoriality in the generating type.
* `TauCeti.freeProC.equivFreeProP`: comparison with the finite-`p` specialization of `freeProC`.

## Main results

* `TauCeti.isProP_freeProP`: a free pro-`p` group is pro-`p`.
* `TauCeti.freeProP.hom_ext`: homomorphisms agreeing on the generators are equal.
* `TauCeti.freeProP.existsUnique_lift`: the universal property.
* `TauCeti.freeProP.lift_surjective`: a topologically generating map lifts to a surjection.
* `TauCeti.freeProP.map_surjective`: a surjection of generating types induces a surjection.
* `TauCeti.freeProP.existsUnique_continuousMulEquiv`: the free pro-`p` group is unique up to a
  unique topological isomorphism matching the generators.
* `TauCeti.freeProC.equivFreeProP_of`: the comparison preserves the generators.

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
noncomputable def fromFreeProfiniteGroup : (p : ℕ) → (X : Type u) →
    freeProfiniteGroup X →ₜ* freeProP p X
  | p, X =>
    ⟨maximalProPQuotient.mk p (freeProfiniteGroup X), maximalProPQuotient.continuous_mk p _⟩

/-- Evaluation of the canonical quotient map agrees with the underlying quotient homomorphism. -/
@[simp low]
theorem fromFreeProfiniteGroup_apply (p : ℕ) (X : Type u) (x : freeProfiniteGroup X) :
    fromFreeProfiniteGroup p X x = maximalProPQuotient.mk p (freeProfiniteGroup X) x := by
  rw [fromFreeProfiniteGroup]
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

end freeProP

/-! ## Comparison with free pro-`C` groups -/

namespace freeProC

variable {p : ℕ} {X Y Z : Type u}

/-- For the class of finite `p`-groups, the free pro-`C` group is canonically isomorphic to the
free pro-`p` group. -/
noncomputable def equivFreeProP (p : ℕ) (X : Type u) :
    freeProC (finiteGroupClassP.{u} p) X ≃ₜ* freeProP p X :=
  proCCompletion.equivMaximalProPQuotient p (freeProfiniteGroup X)

/-- The comparison with the free pro-`p` group commutes with the canonical quotient maps. -/
@[simp]
theorem equivFreeProP_fromFreeProfiniteGroup (p : ℕ) (X : Type u)
    (x : freeProfiniteGroup X) :
    equivFreeProP p X (x : freeProC (finiteGroupClassP p) X) =
      freeProP.fromFreeProfiniteGroup p X x := by
  rw [freeProP.fromFreeProfiniteGroup_apply]
  exact proCCompletion.equivMaximalProPQuotient_mk (p := p)
    (G := freeProfiniteGroup X) x

/-- The comparison with the free pro-`p` group preserves each canonical generator. -/
@[simp]
theorem equivFreeProP_of (p : ℕ) (x : X) :
    equivFreeProP p X (of x) = freeProP.of x := by
  calc
    equivFreeProP p X (of x) =
        equivFreeProP p X (freeProfiniteGroup.of x :
          freeProC (finiteGroupClassP p) X) := by
      congr 1
      rw [← freeProC.fromFreeProfiniteGroup_of,
        freeProC.fromFreeProfiniteGroup_apply]
      rfl
    _ = freeProP.fromFreeProfiniteGroup p X (freeProfiniteGroup.of x) :=
      equivFreeProP_fromFreeProfiniteGroup p X (freeProfiniteGroup.of x)
    _ = freeProP.of x := freeProP.fromFreeProfiniteGroup_of x

/-- The inverse comparison with the free pro-`p` group preserves each canonical generator. -/
@[simp]
theorem equivFreeProP_symm_of (p : ℕ) (x : X) :
    (equivFreeProP p X).symm (freeProP.of x) = of x := by
  apply (equivFreeProP p X).injective
  simp

/-- The inverse comparison commutes with the canonical quotient maps. -/
@[simp]
theorem equivFreeProP_symm_fromFreeProfiniteGroup (p : ℕ) (X : Type u)
    (x : freeProfiniteGroup X) :
    (equivFreeProP p X).symm (x : freeProP p X) =
      (x : freeProC (finiteGroupClassP p) X) := by
  apply (equivFreeProP p X).injective
  simp

end freeProC

namespace freeProP

variable {p : ℕ} {X Y Z : Type u}

section HomExt

variable {Q : Type v} [Group Q] [TopologicalSpace Q] [T2Space Q]

/-- Two continuous homomorphisms out of a free pro-`p` group that agree on the generators are
equal. -/
@[ext]
theorem hom_ext {f g : freeProP p X →ₜ* Q} (h : ∀ x : X, f (of x) = g (of x)) : f = g := by
  let e := freeProC.equivFreeProP p X
  have hcomp : f.comp (e : freeProC (finiteGroupClassP p) X →ₜ* freeProP p X) =
      g.comp (e : freeProC (finiteGroupClassP p) X →ₜ* freeProP p X) :=
    freeProC.hom_ext fun x ↦ by simpa [e] using h x
  apply ContinuousMonoidHom.ext
  intro y
  simpa [e] using DFunLike.congr_fun hcomp (e.symm y)

end HomExt

section Lift

variable {P : Type u} [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [CompactSpace P]
  [TotallyDisconnectedSpace P]

/-- The continuous homomorphism from a free pro-`p` group extending a map on its generators. -/
noncomputable def lift (hP : IsProP p P) (f : X → P) : freeProP p X →ₜ* P :=
  (freeProC.lift (isProC_finiteGroupClassP_iff.mpr hP) f).comp
    ((freeProC.equivFreeProP p X).symm :
      freeProP p X →ₜ* freeProC (finiteGroupClassP p) X)

/-- The free pro-`p` lift recovers the free profinite lift along the quotient map. -/
@[simp]
theorem lift_comp_fromFreeProfiniteGroup (hP : IsProP p P) (f : X → P) :
    (lift hP f).comp (fromFreeProfiniteGroup p X) = freeProfiniteGroup.lift f := by
  apply freeProfiniteGroup.hom_ext
  intro x
  simp [lift]

/-- The free pro-`p` lift evaluates on the image of the free profinite group as the free
profinite lift. -/
@[simp]
theorem lift_fromFreeProfiniteGroup (hP : IsProP p P) (f : X → P)
    (x : freeProfiniteGroup X) :
    lift hP f (x : freeProP p X) = freeProfiniteGroup.lift f x := by
  change freeProC.lift (isProC_finiteGroupClassP_iff.mpr hP) f
      ((freeProC.equivFreeProP p X).symm (x : freeProP p X)) = _
  rw [freeProC.equivFreeProP_symm_fromFreeProfiniteGroup,
    freeProC.lift_fromFreeProfiniteGroup]

/-- The lift of `f` agrees with `f` on every canonical generator. -/
@[simp]
theorem lift_of (hP : IsProP p P) (f : X → P) (x : X) : lift hP f (of x) = f x := by
  simp [lift]

/-- A continuous homomorphism restricting to `f` on the generators is the canonical lift of
`f`. -/
theorem lift_unique (hP : IsProP p P) (f : X → P) (g : freeProP p X →ₜ* P)
    (hg : ∀ x : X, g (of x) = f x) : g = lift hP f :=
  hom_ext fun x ↦ by rw [hg, lift_of]

/-- **The universal property of the free pro-`p` group.** Every map from `X` to a profinite
pro-`p` group extends uniquely to a continuous homomorphism from `freeProP p X`. -/
theorem existsUnique_lift (hP : IsProP p P) (f : X → P) :
    ∃! g : freeProP p X →ₜ* P, ∀ x : X, g (of x) = f x :=
  ⟨lift hP f, lift_of hP f,
    fun g hg ↦ lift_unique (p := p) (X := X) (P := P) hP f g hg⟩

/-- The free pro-`p` lift is natural in its target. -/
@[simp]
theorem comp_lift {Q : Type u} [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [CompactSpace Q] [TotallyDisconnectedSpace Q] (hP : IsProP p P) (hQ : IsProP p Q)
    (g : P →ₜ* Q) (f : X → P) : g.comp (lift hP f) = lift hQ (⇑g ∘ f) :=
  hom_ext fun x ↦ by simp

/-- A map whose range generates the target topologically lifts to a surjection. -/
theorem lift_surjective (hP : IsProP p P) {f : X → P}
    (hf : Dense ((Subgroup.closure (Set.range f) : Subgroup P) : Set P)) :
    Function.Surjective (lift hP f) :=
  (freeProC.lift_surjective (isProC_finiteGroupClassP_iff.mpr hP) hf).comp
    (freeProC.equivFreeProP p X).symm.surjective

end Lift

end freeProP

namespace freeProC

variable {p : ℕ} {X Y Z : Type u}

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

namespace freeProP

variable {p : ℕ} {X Y Z : Type u}

section Map

/-- The continuous homomorphism of free pro-`p` groups induced by a map of generating types. -/
noncomputable def map (f : X → Y) : freeProP p X →ₜ* freeProP p Y :=
  ((freeProC.equivFreeProP p Y :
      freeProC (finiteGroupClassP.{u} p) Y ≃ₜ* freeProP p Y) :
      freeProC (finiteGroupClassP.{u} p) Y →ₜ* freeProP p Y).comp
    ((freeProC.map (C := finiteGroupClassP.{u} p) f).comp
      ((freeProC.equivFreeProP p X).symm :
        freeProP p X →ₜ* freeProC (finiteGroupClassP.{u} p) X))

/-- `map f` carries the generator at `x` to the generator at `f x`. -/
@[simp]
theorem map_of (f : X → Y) (x : X) : map (p := p) f (of x) = of (f x) :=
  by simp [map]

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
      (fromFreeProfiniteGroup p Y).comp (freeProfiniteGroup.map f) := by
  ext x
  simp [map]

/-- The map induced on free pro-`p` groups evaluates compatibly with the map induced on free
profinite groups. -/
@[simp]
theorem map_fromFreeProfiniteGroup (f : X → Y) (x : freeProfiniteGroup X) :
    map (p := p) f (x : freeProP p X) =
      fromFreeProfiniteGroup p Y (freeProfiniteGroup.map f x) :=
  DFunLike.congr_fun (map_comp_fromFreeProfiniteGroup (p := p) f) x

/-- A surjection of generating types induces a surjection of free pro-`p` groups. -/
theorem map_surjective {f : X → Y} (hf : Function.Surjective f) :
    Function.Surjective (map (p := p) f) := by
  intro y
  obtain ⟨cy, rfl⟩ := (freeProC.equivFreeProP p Y).surjective y
  obtain ⟨cx, rfl⟩ := freeProC.map_surjective hf cy
  obtain ⟨x, rfl⟩ := (freeProC.equivFreeProP p X).symm.surjective cx
  exact ⟨x, rfl⟩

end Map

end freeProP

namespace freeProC

variable {p : ℕ} {X Y Z : Type u}

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

end freeProC

namespace freeProP

variable {p : ℕ} {X Y Z : Type u}

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
  have hC : ∀ (P : Type u) [Group P] [TopologicalSpace P] [IsTopologicalGroup P]
      [CompactSpace P] [TotallyDisconnectedSpace P]
      (_hP : IsProC (finiteGroupClassP.{u} p) P) (f : X → P),
        ∃! φ : G →ₜ* P, ∀ x : X, φ (ι x) = f x :=
    fun P _ _ _ _ _ hP f ↦ h P (isProC_finiteGroupClassP_iff.mp hP) f
  obtain ⟨e, he, he_unique⟩ := freeProC.existsUnique_continuousMulEquiv
    (C := finiteGroupClassP.{u} p) (X := X) (G := G)
      (isProC_finiteGroupClassP_iff.mpr hG) ι hC
  let c := freeProC.equivFreeProP p X
  refine ⟨c.symm.trans e, fun x ↦ by simp [c, he x], fun e' he' ↦ ?_⟩
  have hc : c.trans e' = e := he_unique (c.trans e') fun x ↦ by simp [c, he' x]
  apply ContinuousMulEquiv.ext
  intro y
  calc
    e' y = (c.trans e') (c.symm y) := by simp
    _ = e (c.symm y) := by rw [hc]
    _ = (c.symm.trans e) y := rfl

end Uniqueness

end freeProP

end TauCeti
