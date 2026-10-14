/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingSpace.Based
public import TauCeti.Topology.Sphere.Suspension

/-!
# Mapping spaces of the two-sphere as spaces of paths of free loops

Let `𝓛Q = C(S¹, Q)` be the free loop space of `Q`, with the compact-open topology. The sphere `S²`
is the unreduced suspension of `S¹`, so, by currying `I × S¹ → Q` to a path of loops `I → 𝓛Q`:

* `Map(S², Q)` is homeomorphic to the space of paths in `𝓛Q` from a constant loop to a constant
  loop;
* `Map_*(S², Q)`, the maps sending the north pole to `⋆`, is homeomorphic to the space of such
  paths starting at the constant loop at `⋆`.

A path in `𝓛Q` that starts at a constant loop stays in the subspace `𝓛₀Q` of contractible loops,
the loops joined by a path in `𝓛Q` to a constant loop (a union of path components of `𝓛Q`, one for
each path component of `Q`), which is why these are the spaces of paths in `𝓛₀Q` from a constant
loop to a constant loop; the statements here are about paths in `𝓛Q`.

The paths of free loops are taken on the fixed interval `I`.

## Main declarations

* `TauCeti.ConstLoopPath Q`: the space of paths `I → C(S¹, Q)` from a constant loop to a constant
  loop; `TauCeti.constLoopPath_mem_contractibleLoops` says each such path lies in the contractible
  free loops `TauCeti.contractibleLoops Q`, the space `𝓛₀Q`.
* `TauCeti.sphere2HomeomorphConstLoopPath`: `Map(S², Q) ≃ₜ ConstLoopPath Q`.
* `TauCeti.basedMapSphere2HomeomorphBasedConstLoopPath`: `Map_*(S², Q) ≃ₜ` the subspace of
  `ConstLoopPath Q` of paths starting at the constant loop at `⋆`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5.2, the identification of the space of
  paths in `𝓛₀Q` with the double loop space.
-/

public section

noncomputable section

open scoped unitInterval

namespace TauCeti

variable (Q : Type*) [TopologicalSpace Q]

/-- The paths `I → C(S¹, Q)` in the free loop space from a constant loop to a constant loop,
with the compact-open topology. -/
abbrev ConstLoopPath : Type _ :=
  {p : C(I, C(Circle, Q)) // (∃ q, p 0 = ContinuousMap.const Circle q) ∧
    ∃ q, p 1 = ContinuousMap.const Circle q}

variable {Q}

variable (Q) in
/-- The **contractible free loops** `𝓛₀Q ⊆ C(S¹, Q)`: the loops joined by a path in the free loop
space to a constant loop. -/
def contractibleLoops : Set C(Circle, Q) :=
  {γ | ∃ q, Joined γ (ContinuousMap.const Circle q)}

/-- A free loop is contractible exactly when it is joined, by a path in the free loop space, to a
constant loop. -/
@[simp]
theorem mem_contractibleLoops_iff {γ : C(Circle, Q)} :
    γ ∈ contractibleLoops Q ↔ ∃ q, Joined γ (ContinuousMap.const Circle q) :=
  Iff.rfl

/-- Every loop along a path of free loops that starts at a constant loop is contractible: a path
in `ConstLoopPath Q` is a path in `𝓛₀Q`. -/
theorem constLoopPath_mem_contractibleLoops (p : ConstLoopPath Q) (t : I) :
    p.1 t ∈ contractibleLoops Q := by
  obtain ⟨⟨q, hq⟩, -⟩ := p.2
  have h : Joined (0 : I) t := ⟨⟨⟨fun s => s * t, by fun_prop⟩, by simp, by simp⟩⟩
  have h' := h.map p.1.continuous
  rw [hq] at h'
  exact ⟨q, h'.symm⟩

private theorem factorsThrough_suspensionToSphere_iff (g : C(I × Circle, Q)) :
    Function.FactorsThrough g suspensionToSphere ↔
      (∃ q, Homeomorph.curry g 0 = ContinuousMap.const Circle q) ∧
        ∃ q, Homeomorph.curry g 1 = ContinuousMap.const Circle q := by
  -- currying evaluates a map on the product pointwise
  have hc (t : I) (z : Circle) : Homeomorph.curry g t z = g (t, z) := rfl
  constructor
  · intro h
    have hend (t : I) (e : ∀ z, suspensionToSphere (t, z) = suspensionToSphere (t, 1)) :
        ∃ q, Homeomorph.curry g t = ContinuousMap.const Circle q :=
      ⟨g (t, 1), ContinuousMap.ext fun z => by rw [hc]; exact h (e z)⟩
    refine ⟨hend 0 fun z => ?_, hend 1 fun z => ?_⟩
    · exact (suspensionToSphere_eq_north_iff _).2 rfl |>.trans
        ((suspensionToSphere_eq_north_iff (0, 1)).2 rfl).symm
    · exact (suspensionToSphere_eq_south_iff _).2 rfl |>.trans
        ((suspensionToSphere_eq_south_iff (1, 1)).2 rfl).symm
  · rintro ⟨⟨q₀, h₀⟩, ⟨q₁, h₁⟩⟩ p p' hp
    have e₀ (p : I × Circle) (hp : p.1 = 0) : g p = q₀ := by
      have := DFunLike.congr_fun h₀ p.2
      rwa [hc, ← hp] at this
    have e₁ (p : I × Circle) (hp : p.1 = 1) : g p = q₁ := by
      have := DFunLike.congr_fun h₁ p.2
      rwa [hc, ← hp] at this
    rcases eq_or_of_suspensionToSphere_eq hp with rfl | ⟨h, h'⟩ | ⟨h, h'⟩
    · rfl
    · rw [e₀ _ h, e₀ _ h']
    · rw [e₁ _ h, e₁ _ h']

/-- **`Map(S², Q)` is the space of paths of free loops from a constant loop to a constant
loop.** Precomposition with the suspension map `I × S¹ → S²`, followed by currying. -/
def sphere2HomeomorphConstLoopPath : C(Sphere2, Q) ≃ₜ ConstLoopPath Q :=
  (ContinuousMap.homeomorphFactorsThrough suspensionToSphere suspensionToSphere_surjective).trans
    (Homeomorph.subtype Homeomorph.curry factorsThrough_suspensionToSphere_iff)

@[simp]
theorem sphere2HomeomorphConstLoopPath_apply (f : C(Sphere2, Q)) (t : I) (z : Circle) :
    (sphere2HomeomorphConstLoopPath f).1 t z = f (suspensionToSphere (t, z)) := by
  rw [sphere2HomeomorphConstLoopPath, Homeomorph.trans_apply]
  rw [Homeomorph.subtype_apply_coe, ContinuousMap.homeomorphFactorsThrough_apply]
  exact ContinuousMap.curry_apply (f.comp suspensionToSphere) t z

/-- The inverse of `sphere2HomeomorphConstLoopPath` evaluates, at the image of `(t, z)` under the
suspension map, to the value of the path of loops at `t` and `z`. -/
@[simp]
theorem sphere2HomeomorphConstLoopPath_symm_apply (p : ConstLoopPath Q) (t : I) (z : Circle) :
    sphere2HomeomorphConstLoopPath.symm p (suspensionToSphere (t, z)) = p.1 t z := by
  have h := sphere2HomeomorphConstLoopPath_apply
    (sphere2HomeomorphConstLoopPath.symm p) t z
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

variable (Q) in
/-- The paths in the free loop space from the constant loop at `x` to a constant loop. -/
abbrev BasedConstLoopPath (x : Q) : Type _ :=
  {p : ConstLoopPath Q // p.1 0 = ContinuousMap.const Circle x}

/-- **`Map_*(S², Q)` is the space of paths of free loops from the constant loop at `x` to a
constant loop.** The north pole of `S²` goes to `x`; the south pole is free. -/
def basedMapSphere2HomeomorphBasedConstLoopPath (x : Q) :
    BasedMap Sphere2 Q Sphere2.north x ≃ₜ BasedConstLoopPath Q x :=
  Homeomorph.subtype sphere2HomeomorphConstLoopPath fun f => by
    constructor
    · intro h
      refine ContinuousMap.ext fun z => ?_
      rw [sphere2HomeomorphConstLoopPath_apply, ContinuousMap.const_apply,
        (suspensionToSphere_eq_north_iff _).2 rfl, h]
    · intro h
      have := DFunLike.congr_fun h 1
      rwa [sphere2HomeomorphConstLoopPath_apply, ContinuousMap.const_apply,
        (suspensionToSphere_eq_north_iff (0, 1)).2 rfl] at this

@[simp]
theorem basedMapSphere2HomeomorphBasedConstLoopPath_apply (x : Q)
    (f : BasedMap Sphere2 Q Sphere2.north x) (t : I) (z : Circle) :
    (basedMapSphere2HomeomorphBasedConstLoopPath x f).1.1 t z =
      f.1 (suspensionToSphere (t, z)) :=
  sphere2HomeomorphConstLoopPath_apply f.1 t z

/-- The inverse of `basedMapSphere2HomeomorphBasedConstLoopPath` evaluates, at the image of
`(t, z)` under the suspension map, to the value of the path of loops at `t` and `z`. -/
@[simp]
theorem basedMapSphere2HomeomorphBasedConstLoopPath_symm_apply (x : Q)
    (p : BasedConstLoopPath Q x) (t : I) (z : Circle) :
    ((basedMapSphere2HomeomorphBasedConstLoopPath x).symm p).1 (suspensionToSphere (t, z)) =
      p.1.1 t z := by
  have h := basedMapSphere2HomeomorphBasedConstLoopPath_apply x
    ((basedMapSphere2HomeomorphBasedConstLoopPath x).symm p) t z
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

end TauCeti
