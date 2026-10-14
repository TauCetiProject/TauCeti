/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.MappingSpace.Based
public import TauCeti.Topology.MappingSpace.FreeLoop
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
  free loops `TauCeti.contractibleLoops Q`, the space `𝓛₀Q`, in which the constant loops embed
  (`TauCeti.isEmbedding_constContractibleLoop`).
* `TauCeti.sphere2HomeomorphConstLoopPath`: `Map(S², Q) ≃ₜ ConstLoopPath Q`, and
  `TauCeti.sphere2HomeomorphContractibleConstLoopPath`: `Map(S², Q) ≃ₜ` the paths in `𝓛₀Q` from a
  constant loop to a constant loop.
* `TauCeti.basedMapSphere2HomeomorphBasedConstLoopPath`: `Map_*(S², Q) ≃ₜ` the subspace of
  `ConstLoopPath Q` of paths starting at the constant loop at `⋆`, and
  `TauCeti.basedMapSphere2HomeomorphBasedContractibleConstLoopPath` the same in `𝓛₀Q`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §5.2, the identification of the space of
  paths in `𝓛₀Q` with the double loop space.
-/

public section

noncomputable section

open scoped unitInterval

namespace TauCeti

variable {Q : Type*} [TopologicalSpace Q]

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

/-- **`Map(S², Q)` is the space of paths in the contractible free loops `𝓛₀Q` from a constant loop
to a constant loop.** -/
def sphere2HomeomorphContractibleConstLoopPath : C(Sphere2, Q) ≃ₜ ContractibleConstLoopPath Q :=
  sphere2HomeomorphConstLoopPath.trans constLoopPathHomeomorph

/-- The loop of the path of contractible loops at `(t, z)` is the value of the sphere map at the
image of `(t, z)` under the suspension map. -/
@[simp]
theorem sphere2HomeomorphContractibleConstLoopPath_apply (f : C(Sphere2, Q)) (t : I)
    (z : Circle) :
    ((sphere2HomeomorphContractibleConstLoopPath f).1 t : C(Circle, Q)) z =
      f (suspensionToSphere (t, z)) := by
  rw [sphere2HomeomorphContractibleConstLoopPath, Homeomorph.trans_apply,
    coe_constLoopPathHomeomorph]
  exact sphere2HomeomorphConstLoopPath_apply f t z

/-- **`Map_*(S², Q)` is the space of paths in the contractible free loops from the constant loop at
`x` to a constant loop.** -/
def basedMapSphere2HomeomorphBasedContractibleConstLoopPath (x : Q) :
    BasedMap Sphere2 Q Sphere2.north x ≃ₜ BasedContractibleConstLoopPath Q x :=
  (basedMapSphere2HomeomorphBasedConstLoopPath x).trans
    (Homeomorph.subtype constLoopPathHomeomorph fun p => by
      constructor
      · intro h
        exact Subtype.ext (((coe_constLoopPathHomeomorph p 0).trans h).trans
          (coe_constContractibleLoop x).symm)
      · intro h
        exact (coe_constLoopPathHomeomorph p 0).symm.trans
          ((congrArg Subtype.val h).trans (coe_constContractibleLoop x)))

/-- The inverse of `sphere2HomeomorphContractibleConstLoopPath` evaluates, at the image of `(t, z)`
under the suspension map, to the value of the path of contractible loops at `t` and `z`. -/
@[simp]
theorem sphere2HomeomorphContractibleConstLoopPath_symm_apply
    (r : ContractibleConstLoopPath Q) (t : I) (z : Circle) :
    sphere2HomeomorphContractibleConstLoopPath.symm r (suspensionToSphere (t, z)) =
      (r.1 t : C(Circle, Q)) z := by
  have h := sphere2HomeomorphContractibleConstLoopPath_apply
    (sphere2HomeomorphContractibleConstLoopPath.symm r) t z
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

/-- The loop of the path of contractible loops at `(t, z)` is the value of the based sphere map at
the image of `(t, z)` under the suspension map. -/
@[simp]
theorem basedMapSphere2HomeomorphBasedContractibleConstLoopPath_apply (x : Q)
    (f : BasedMap Sphere2 Q Sphere2.north x) (t : I) (z : Circle) :
    ((basedMapSphere2HomeomorphBasedContractibleConstLoopPath x f).1.1 t : C(Circle, Q)) z =
      f.1 (suspensionToSphere (t, z)) := by
  rw [basedMapSphere2HomeomorphBasedContractibleConstLoopPath, Homeomorph.trans_apply,
    Homeomorph.subtype_apply_coe, coe_constLoopPathHomeomorph]
  exact basedMapSphere2HomeomorphBasedConstLoopPath_apply x f t z

/-- The inverse of `basedMapSphere2HomeomorphBasedContractibleConstLoopPath` evaluates, at the
image of `(t, z)` under the suspension map, to the value of the path of contractible loops at `t`
and `z`. -/
@[simp]
theorem basedMapSphere2HomeomorphBasedContractibleConstLoopPath_symm_apply (x : Q)
    (p : BasedContractibleConstLoopPath Q x) (t : I) (z : Circle) :
    ((basedMapSphere2HomeomorphBasedContractibleConstLoopPath x).symm p).1
        (suspensionToSphere (t, z)) = (p.1.1 t : C(Circle, Q)) z := by
  have h := basedMapSphere2HomeomorphBasedContractibleConstLoopPath_apply x
    ((basedMapSphere2HomeomorphBasedContractibleConstLoopPath x).symm p) t z
  rw [Homeomorph.apply_symm_apply] at h
  exact h.symm

end TauCeti
