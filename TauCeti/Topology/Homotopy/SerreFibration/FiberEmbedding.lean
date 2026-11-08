/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.HomotopyGroup.Homeomorph
public import TauCeti.Topology.Homotopy.SerreFibration.Exact

/-!
# The exact homotopy sequence with a fibre given by an embedding

The exact homotopy sequence of a Serre fibration `p : E → B`
(`TauCeti.Topology.Homotopy.SerreFibration.Exact`) is stated for the fibre `p⁻¹(b)` itself, with
the subspace topology. In examples the fibre is usually known as another space `F` embedded in
`E`, such as the block subgroup `SO(n) ⊆ SO(n + 1)` in the bundle `SO(n + 1) → Sⁿ`. This file
restates the sequence

`π_{n+1}(E, e) → π_{n+1}(B, b) → π_n(F, x) → π_n(E, e) → π_n(B, b)`

for a topological embedding `j : F → E` whose range is the fibre `p⁻¹(b)`, with `j x = e`. The
fibre map is `j` itself. The boundary map
`∂ : π_{n+1}(B, b) → π_n(F, x)` (`TauCeti.TopCat.fibrationBoundaryOfIsEmbedding`) is the boundary
map of `p` followed by the homeomorphism of the fibre with `F`
(`TauCeti.TopCat.fiberHomeomorphOfIsEmbedding`, in `TauCeti.Topology.Category.TopCat.Fiber`). For
`n ≥ 1` it is a group homomorphism (`TauCeti.TopCat.fibrationBoundaryOfIsEmbeddingHom`).

## Main definitions

* `TauCeti.TopCat.fibrationBoundaryOfIsEmbedding`: the boundary map `π_{n+1}(B, b) → π_n(F, x)`.

## Main results

* `TauCeti.TopCat.mem_range_fibrationBoundaryOfIsEmbedding_iff`: exactness at `π_n(F, x)`.
* `TauCeti.TopCat.mem_range_homotopyGroupMap_iff_of_isEmbedding`: exactness at `π_n(E, e)`.
* `TauCeti.TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundaryOfIsEmbedding_eq`: exactness at
  `π_{n+1}(B, b)`.

## References

* A. Hatcher, *Algebraic Topology*, Theorem 4.41.
-/

public section

noncomputable section

open CategoryTheory Set Topology
open scoped Topology.Homotopy

universe u

namespace TauCeti.TopCat

variable {E B : _root_.TopCat.{u}} {p : E ⟶ B} {b : B} {F : Type*} [TopologicalSpace F]
  {j : C(F, E)} {N : Type*}

variable (hp : serreFibrations p) (hj : IsEmbedding j) (hjr : range j = p ⁻¹' {b})
  {x : F} {e : p.fiber b} (hx : j x = e)

/-- The **boundary map** `∂ : π_{n+1}(B, b) → π_n(F, x)` of a Serre fibration `p` whose fibre over
`b` is the image of an embedding `j : F → E`, with `j x = e`: the boundary map of `p`
(`TauCeti.TopCat.fibrationBoundary`) followed by the inverse of the homeomorphism of `F` with the
fibre. -/
def fibrationBoundaryOfIsEmbedding [Finite N] :
    HomotopyGroup (Option N) B b → HomotopyGroup N F x :=
  (HomotopyGroup.homeomorphEquivOfEq (fiberHomeomorphOfIsEmbedding hj hjr)
    (fiberHomeomorphOfIsEmbedding_apply_eq hj hjr hx)).symm ∘ fibrationBoundary hp e

/-- The boundary map with fibre `F` is the boundary map of `p` followed by the inverse of the
homeomorphism of `F` with the fibre. -/
theorem fibrationBoundaryOfIsEmbedding_apply [Finite N] (a : HomotopyGroup (Option N) B b) :
    fibrationBoundaryOfIsEmbedding hp hj hjr hx a =
      (HomotopyGroup.homeomorphEquivOfEq (fiberHomeomorphOfIsEmbedding hj hjr)
        (fiberHomeomorphOfIsEmbedding_apply_eq hj hjr hx)).symm (fibrationBoundary hp e a) :=
  (rfl)

/-- The boundary map sends the class of the constant loop to the class of the constant loop. -/
@[simp]
theorem fibrationBoundaryOfIsEmbedding_const [Finite N] :
    fibrationBoundaryOfIsEmbedding hp hj hjr hx (⟦GenLoop.const⟧ : HomotopyGroup (Option N) B b) =
      ⟦GenLoop.const⟧ :=
  (congrArg _ (fibrationBoundary_const hp)).trans
    ((HomotopyGroup.map_mk _ _ GenLoop.const).trans (congrArg _ (GenLoop.map_const _ _)))

include hx in
/-- The map induced by `j` on homotopy groups is the map induced by the fibre inclusion, read
through the homeomorphism of `F` with the fibre. -/
theorem homotopyGroupMap_eq_map_fiberι (a : HomotopyGroup N F x) :
    HomotopyGroup.map j hx a =
      HomotopyGroup.map (p.fiberι b).hom (TopCat.Hom.fiberι_apply p b e)
        (HomotopyGroup.homeomorphEquivOfEq (fiberHomeomorphOfIsEmbedding hj hjr)
          (fiberHomeomorphOfIsEmbedding_apply_eq hj hjr hx) a) := by
  rw [HomotopyGroup.homeomorphEquivOfEq_apply, HomotopyGroup.map_comp_apply]
  exact HomotopyGroup.map_congr (ContinuousMap.ext fun _ => ((TopCat.Hom.fiberι_apply p b _).trans
    (coe_fiberHomeomorphOfIsEmbedding_apply hj hjr _)).symm) _ _ a

/-- **Exactness at `π_n(F, x)`.** A class of `F` is a boundary exactly when it becomes trivial in
`π_n(E, e)`. -/
theorem mem_range_fibrationBoundaryOfIsEmbedding_iff [Finite N] {a : HomotopyGroup N F x} :
    a ∈ range (fibrationBoundaryOfIsEmbedding hp hj hjr hx) ↔
      HomotopyGroup.map j hx a = (⟦GenLoop.const⟧ : HomotopyGroup N E e) := by
  set φ := HomotopyGroup.homeomorphEquivOfEq (N := N) (fiberHomeomorphOfIsEmbedding hj hjr)
    (fiberHomeomorphOfIsEmbedding_apply_eq hj hjr hx)
  rw [homotopyGroupMap_eq_map_fiberι hj hjr hx, ← mem_range_fibrationBoundary_iff hp]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨c, (φ.apply_symm_apply _).symm⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, φ.symm_apply_eq.2 hc⟩

include hp hj hjr in
/-- **Exactness at `π_n(E, e)`.** A class of `E` comes from `F` exactly when it becomes trivial in
`π_n(B, b)`. -/
theorem mem_range_homotopyGroupMap_iff_of_isEmbedding [Finite N] {a : HomotopyGroup N E e} :
    a ∈ range (HomotopyGroup.map (N := N) j hx) ↔
      HomotopyGroup.map p.hom (Set.mem_singleton_iff.1 e.2) a =
        (⟦GenLoop.const⟧ : HomotopyGroup N B b) := by
  set φ := HomotopyGroup.homeomorphEquivOfEq (N := N) (fiberHomeomorphOfIsEmbedding hj hjr)
    (fiberHomeomorphOfIsEmbedding_apply_eq hj hjr hx)
  rw [← mem_range_homotopyGroupMap_fiberι_iff hp]
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨φ c, (homotopyGroupMap_eq_map_fiberι hj hjr hx c).symm⟩
  · rintro ⟨c, rfl⟩
    refine ⟨φ.symm c, ?_⟩
    rw [homotopyGroupMap_eq_map_fiberι hj hjr hx, φ.apply_symm_apply]

/-- **Exactness at `π_{n+1}(B, b)`.** A class of the base comes from the total space exactly when
its boundary in `π_n(F, x)` is trivial. -/
theorem mem_range_homotopyGroupMap_iff_fibrationBoundaryOfIsEmbedding_eq [Finite N]
    {a : HomotopyGroup (Option N) B b} :
    a ∈ range (HomotopyGroup.map p.hom (Set.mem_singleton_iff.1 e.2)) ↔
      fibrationBoundaryOfIsEmbedding hp hj hjr hx a =
        (⟦GenLoop.const⟧ : HomotopyGroup N F x) := by
  have hφ := fiberHomeomorphOfIsEmbedding_apply_eq hj hjr hx
  -- The homeomorphism sends the trivial class of `F` to the trivial class of the fibre.
  have hconst : HomotopyGroup.homeomorphEquivOfEq (fiberHomeomorphOfIsEmbedding hj hjr) hφ
      (⟦GenLoop.const⟧ : HomotopyGroup N F x) = ⟦GenLoop.const⟧ :=
    (HomotopyGroup.map_mk _ hφ GenLoop.const).trans (congrArg _ (GenLoop.map_const _ hφ))
  rw [mem_range_homotopyGroupMap_iff_fibrationBoundary_eq hp, fibrationBoundaryOfIsEmbedding_apply,
    ← hconst]
  exact (Equiv.symm_apply_eq _).symm

/-- For `n ≥ 1`, the boundary map `π_{n+1}(B, b) → π_n(F, x)` of a Serre fibration whose fibre is
the image of an embedding `j : F → E`, as a group homomorphism. -/
def fibrationBoundaryOfIsEmbeddingHom [DecidableEq N] [Finite N] [Nonempty N] :
    HomotopyGroup (Option N) B b →* HomotopyGroup N F x :=
  (HomotopyGroup.homeomorphMulEquivOfEq (fiberHomeomorphOfIsEmbedding hj hjr)
    (fiberHomeomorphOfIsEmbedding_apply_eq hj hjr hx)).symm.toMonoidHom.comp
    (fibrationBoundaryHom hp e)

@[simp]
theorem coe_fibrationBoundaryOfIsEmbeddingHom [DecidableEq N] [Finite N] [Nonempty N] :
    ⇑(fibrationBoundaryOfIsEmbeddingHom (N := N) hp hj hjr hx) =
      fibrationBoundaryOfIsEmbedding hp hj hjr hx := by
  funext a
  simp only [fibrationBoundaryOfIsEmbeddingHom, fibrationBoundaryOfIsEmbedding_apply,
    MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
    HomotopyGroup.homeomorphMulEquivOfEq_symm_apply, HomotopyGroup.homeomorphEquivOfEq_symm_apply]
  exact congrArg _ (congrFun (coe_fibrationBoundaryHom hp e) a)

end TauCeti.TopCat
