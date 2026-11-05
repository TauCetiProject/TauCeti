/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.FiniteDimensional
public import TauCeti.Analysis.Normed.Module.Alternating.TopDegree
public import TauCeti.LinearAlgebra.Orientation.Transverse
public import TauCeti.Topology.VectorBundle.Orientation.Basic
public import TauCeti.Topology.VectorBundle.Subbundle

/-!
# Orientations of codimension-one subbundles transverse to a section

Let `E → B` be a real vector bundle of rank `k + 1` with an orientation `o`, and let `V` be a
subbundle of rank `k`: a family of subspaces `V b ⊆ E b`, itself a vector bundle whose total
space maps continuously into that of `E`. A continuous section `ν` of `E` that is nowhere tangent
to `V` (`ν b ∉ V b`) then orients `V`: at every point, `V b` carries the orientation induced by
`o b` and the transverse vector `ν b` (`Orientation.transverse`), in which a basis `v₁, …, vₖ` of
`V b` is positive exactly when `ν b, v₁, …, vₖ` is a positive basis of `E b`. These fibre
orientations vary continuously (`TauCeti.VectorBundleOrientation.transverse`).

For the tangent bundle of an oriented manifold and the tangent field of a codimension-one
foliation, a transverse vector field is a coorientation of the foliation, and this is how an
orientation and a coorientation together orient the leaves. The orientation feeds the Thom class
and Euler class of the subbundle.

The proof of continuity reads everything in local trivializations near a point `b₀`. A
trivialization of `V` gives a continuous frame `s₁, …, sₖ` of `V`; read in a trivialization of
`E`, the vectors `ν, s₁, …, sₖ` give a continuous family of bases of the model fibre, whose
determinant has locally constant sign. Since `o` is locally constant in the trivialization of `E`,
so is the induced orientation in the frame of `V`.

## Main definitions

* `TauCeti.VectorBundleOrientation.transverse`: the orientation of a codimension-one subbundle
  induced by an orientation of the ambient bundle and a continuous section nowhere tangent to the
  subbundle.

## Main results

* `TauCeti.VectorBundleOrientation.transverse_apply`: on each fibre it is the orientation induced
  by the fibre orientation and the transverse vector.
* `TauCeti.VectorBundleOrientation.transverse_neg`: reversing the ambient orientation reverses
  it.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 15
  (Proposition 15.21, orientations of hypersurfaces induced by a transverse vector field).
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §9 (oriented vector bundles).
-/

public section

noncomputable section

open Bundle Filter Module Set
open scoped Topology

namespace TauCeti.VectorBundleOrientation

variable {B : Type*} [TopologicalSpace B]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type*} [TopologicalSpace (TotalSpace F E)] [∀ b, AddCommGroup (E b)]
  [∀ b, Module ℝ (E b)] [∀ b, TopologicalSpace (E b)] [FiberBundle F E] [VectorBundle ℝ F E]
  {F' : Type*} [NormedAddCommGroup F'] [NormedSpace ℝ F']
  {V : ∀ b, Submodule ℝ (E b)} [TopologicalSpace (TotalSpace F' fun b ↦ V b)]
  [FiberBundle F' fun b ↦ V b] [VectorBundle ℝ F' fun b ↦ V b] {k : ℕ}

/-- The fibrewise orientations of the subbundle induced by `o` and `ν`. -/
private def fiberTransverse (hF : finrank ℝ F = k + 1) (hF' : finrank ℝ F' = k)
    (o : VectorBundleOrientation F E (Fin (k + 1))) {ν : ∀ b, E b} (hνV : ∀ b, ν b ∉ V b)
    (b : B) : Orientation ℝ (V b) (Fin k) :=
  (o b).transverse ((VectorBundle.finrank_eq ℝ F E b).trans hF)
    ((VectorBundle.finrank_eq ℝ F' (fun b ↦ V b) b).trans hF') (hνV b)

variable [FiniteDimensional ℝ F] [FiniteDimensional ℝ F']

/-- **The induced fibre orientations are locally constant** in the preferred trivializations of
the subbundle. -/
private theorem eventually_mapOrientation_fiberTransverse (hF : finrank ℝ F = k + 1)
    (hF' : finrank ℝ F' = k)
    (hV : Continuous fun p : TotalSpace F' (fun b ↦ V b) ↦ (⟨p.proj, p.2⟩ : TotalSpace F E))
    (o : VectorBundleOrientation F E (Fin (k + 1))) {ν : ∀ b, E b}
    (hν : Continuous fun b ↦ (⟨b, ν b⟩ : TotalSpace F E)) (hνV : ∀ b, ν b ∉ V b) (b₀ : B) :
    ∀ᶠ x in 𝓝 b₀, ∀ hx : x ∈ (trivializationAt F' (fun b ↦ V b) b₀).baseSet,
      (trivializationAt F' (fun b ↦ V b) b₀).mapOrientation (Fin k) hx
          (fiberTransverse hF hF' o hνV x) =
        (trivializationAt F' (fun b ↦ V b) b₀).mapOrientation (Fin k)
          (FiberBundle.mem_baseSet_trivializationAt' b₀) (fiberTransverse hF hF' o hνV b₀) := by
  set e' := trivializationAt F' (fun b ↦ V b) b₀
  set g := trivializationAt F E b₀
  have he' : b₀ ∈ e'.baseSet := FiberBundle.mem_baseSet_trivializationAt' b₀
  have hg : b₀ ∈ g.baseSet := FiberBundle.mem_baseSet_trivializationAt' b₀
  let β' := finBasisOfFinrankEq ℝ F' hF'
  let β := finBasisOfFinrankEq ℝ F hF
  -- The transverse section followed by the frame `e'.symm x (β' j)` of `V`, read in `g`.
  let w : B → Fin (k + 1) → F := fun x ↦
    Fin.cons (g ⟨x, ν x⟩).2 fun j ↦ (g ⟨x, (e'.symm x (β' j) : E x)⟩).2
  let d : B → ℝ := fun x ↦ β.det (w x)
  -- At a point of both base sets, `d x` is the determinant of `ν x` followed by the frame,
  -- with respect to the basis of `E x` carried from `β` by `g`.
  have hdet (x : B) (hx : x ∈ e'.baseSet) (hxg : x ∈ g.baseSet) :
      (β.map (g.linearEquivAt ℝ x hxg).symm).det
          (Fin.cons (ν x) ((V x).subtype ∘ β'.map (e'.linearEquivAt ℝ x hx).symm)) = d x := by
    rw [Basis.det_map, LinearEquiv.symm_symm, Fin.comp_cons]
    simp only [d, w, Function.comp_def, Basis.map_apply, Submodule.subtype_apply,
      Trivialization.linearEquivAt_apply, Trivialization.linearEquivAt_symm_apply]
  -- So the induced orientation is read as `β'` exactly when the sign of `d x` matches whether `o x`
  -- is read as `β`.
  have hread (x : B) (hx : x ∈ e'.baseSet) (hxg : x ∈ g.baseSet) :
      e'.mapOrientation (Fin k) hx (fiberTransverse hF hF' o hνV x) = β'.orientation ↔
        (g.mapOrientation (Fin (k + 1)) hxg (o x) = β.orientation ↔ 0 < d x) := by
    rw [Trivialization.mapOrientation_eq_orientation_iff,
      Trivialization.mapOrientation_eq_orientation_iff, fiberTransverse,
      Orientation.transverse_eq_orientation_iff_det, hdet x hx hxg]
  -- The determinant `d` is continuous at `b₀` and nonzero there.
  have hw : ContinuousAt w b₀ := by
    refine continuousAt_pi.2 fun i ↦ Fin.cases ?_ (fun j ↦ ?_) i
    · simp only [w, Fin.cons_zero]
      exact ((g.continuousOn.continuousAt (g.open_source.mem_nhds (g.mem_source.2 hg))).comp
        hν.continuousAt).snd
    · simp only [w, Fin.cons_succ]
      exact e'.continuousAt_symm_subbundle g hV he' hg (β' j)
  have hd₀ : d b₀ ≠ 0 := by
    rw [← hdet b₀ he' hg]
    exact Basis.det_finCons_ne_zero _ _ (hνV b₀)
  have hd : ContinuousAt d b₀ := by
    have h := (map_continuous β.continuousDet).continuousAt.comp hw
    simpa only [Function.comp_def, Basis.continuousDet_apply] using h
  have hpos : ∀ᶠ x in 𝓝 b₀, 0 < d x * d b₀ :=
    (hd.mul continuousAt_const).eventually (lt_mem_nhds (mul_self_pos.2 hd₀))
  filter_upwards [hpos, o.eventually_mapOrientation_eq (by rw [Fintype.card_fin, hF]) g hg,
    g.open_baseSet.mem_nhds hg] with x hxpos hxo hxg hx
  rw [β'.eq_iff_eq_orientation_iff, hread x hx hxg, hread b₀ he' hg, hxo hxg,
    pos_iff_pos_of_mul_pos hxpos]

/-- **The orientation of a codimension-one subbundle induced by a transverse section.** Let `o` be
an orientation of a real vector bundle `E` of rank `k + 1`, let `V` be a subbundle of rank `k`
whose total space maps continuously into that of `E`, and let `ν` be a continuous section of `E`
with `ν b ∉ V b` everywhere. Then `V` is oriented by declaring a basis `v₁, …, vₖ` of `V b`
positive exactly when `ν b, v₁, …, vₖ` is a positive basis of `E b`. -/
def transverse (hF : finrank ℝ F = k + 1) (hF' : finrank ℝ F' = k)
    (hV : Continuous fun p : TotalSpace F' (fun b ↦ V b) ↦ (⟨p.proj, p.2⟩ : TotalSpace F E))
    (o : VectorBundleOrientation F E (Fin (k + 1))) {ν : ∀ b, E b}
    (hν : Continuous fun b ↦ (⟨b, ν b⟩ : TotalSpace F E)) (hνV : ∀ b, ν b ∉ V b) :
    VectorBundleOrientation F' (fun b ↦ V b) (Fin k) :=
  ofEventually (by rw [Fintype.card_fin, hF']) (fiberTransverse hF hF' o hνV)
    (fun b ↦ trivializationAt F' (fun b ↦ V b) b)
    (fun b ↦ FiberBundle.mem_baseSet_trivializationAt' b)
    (eventually_mapOrientation_fiberTransverse hF hF' hV o hν hνV)

variable (hF : finrank ℝ F = k + 1) (hF' : finrank ℝ F' = k)
  (hV : Continuous fun p : TotalSpace F' (fun b ↦ V b) ↦ (⟨p.proj, p.2⟩ : TotalSpace F E))
  (o : VectorBundleOrientation F E (Fin (k + 1))) {ν : ∀ b, E b}
  (hν : Continuous fun b ↦ (⟨b, ν b⟩ : TotalSpace F E)) (hνV : ∀ b, ν b ∉ V b)

/-- On each fibre, the transverse orientation is the orientation of `V b` induced by `o b` and the
transverse vector `ν b`. -/
theorem transverse_apply (b : B) (hE : finrank ℝ (E b) = k + 1) (hVb : finrank ℝ (V b) = k) :
    transverse hF hF' hV o hν hνV b = (o b).transverse hE hVb (hνV b) := by
  rw [transverse, coe_ofEventually, fiberTransverse]

/-- Reversing the orientation of the ambient bundle reverses the transverse orientation of the
subbundle. -/
@[simp]
theorem transverse_neg : transverse hF hF' hV (-o) hν hνV = -transverse hF hF' hV o hν hνV := by
  ext b
  have hE := (VectorBundle.finrank_eq ℝ F E b).trans hF
  have hVb := (VectorBundle.finrank_eq ℝ F' (fun b ↦ V b) b).trans hF'
  rw [neg_apply, transverse_apply hF hF' hV _ hν hνV b hE hVb,
    transverse_apply hF hF' hV _ hν hνV b hE hVb, neg_apply, Orientation.transverse_neg]

end TauCeti.VectorBundleOrientation
