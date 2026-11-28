/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Structure
public import TauCeti.Topology.Homeomorph.Congr
import TauCeti.AlgebraicTopology.SimplicialComplex.Realization.ImageComplex
import TauCeti.Topology.PL.Inverse.Polyhedron

/-!
# Homeomorphisms of finite PL structures

A homeomorphism which is piecewise linear for finite PL structures has a piecewise-linear
inverse. In barycentric coordinates this is the inverse theorem for maps of finite polyhedra;
no manifold property of the triangulations is used by the inversion argument.

Consequently the PL self-homeomorphisms form a subgroup of the homeomorphism group. Transporting
a PL structure along a homeomorphism transports this subgroup by conjugation. This is the group
of representatives used in forming PL mapping classes.

## References

* C. P. Rourke and B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer
  (1972), Chapters 1–2.
-/

public noncomputable section

open Set AbstractSimplicialComplex

namespace TauCeti.PLStructure

universe u v

variable {M : Type u} {N : Type v} [TopologicalSpace M] [TopologicalSpace N]
  {m n : ℕ} {s : PLStructure M m} {t : PLStructure N n}

/-- A PL homeomorphism between finite PL structures has a PL inverse. Only the forward map
needs to be checked. -/
theorem IsPLMap.symm {f : M ≃ₜ N} (hf : s.IsPLMap t f) : t.IsPLMap s f.symm := by
  classical
  let := Fintype.ofFinite s.ι
  let := Fintype.ofFinite t.ι
  obtain ⟨F, hF, hFf⟩ := isPLMap_iff.mp hf
  let G : (t.ι → ℝ) → (s.ι → ℝ) := Function.extend
    (fun y : Realization t.K => (y.val : t.ι → ℝ))
    (fun y => ((s.e.symm (f.symm (t.e y))).val : s.ι → ℝ)) 0
  have hG (y : Realization t.K) : G (y.val : t.ι → ℝ) =
      ((s.e.symm (f.symm (t.e y))).val : s.ι → ℝ) :=
    (injective_realization_coe t.K).extend_apply _ _ y
  obtain ⟨K, hK, hspace⟩ := s.K.exists_finite_space_eq_range_realization_coe
  have hleft : LeftInvOn G F K.space := by
    rw [hspace]
    rintro _ ⟨x, rfl⟩
    simp only [hFf, hG, Homeomorph.apply_symm_apply, Homeomorph.symm_apply_apply]
  have himage : F '' K.space = range fun y : Realization t.K => (y.val : t.ι → ℝ) := by
    rw [hspace, ← range_comp]
    exact (congrArg range (funext hFf)).trans
      (EquivLike.range_comp (fun y : Realization t.K => (y.val : t.ι → ℝ))
        ((s.e.trans f).trans t.e.symm))
  have hF' : IsPLOn F K.space := by
    rwa [hspace]
  have hG' := hF'.inverse_of_leftInvOn (K := K) (g := G) hK hleft
  rw [himage] at hG'
  exact isPLMap_iff.mpr ⟨G, hG', hG⟩

/-- PL regularity of a homeomorphism is equivalent to PL regularity of its inverse. -/
@[simp]
theorem isPLMap_symm_iff {f : M ≃ₜ N} : t.IsPLMap s f.symm ↔ s.IsPLMap t f :=
  ⟨fun h => by simpa only [Homeomorph.symm_symm] using h.symm, fun h => h.symm⟩

/-- The PL self-homeomorphisms of a finite PL structure. Inverse regularity follows from
`TauCeti.PLStructure.IsPLMap.symm`, so only forward regularity is required for membership. -/
def plHomeomorphSubgroup (s : PLStructure M n) : Subgroup (M ≃ₜ M) where
  carrier := {f | s.IsPLMap s f}
  one_mem' := by
    rw [Set.mem_ofPred_eq, funext (Homeomorph.one_apply (X := M))]
    exact s.isPLMap_id
  mul_mem' {f g} hf hg := by
    rw [Set.mem_ofPred_eq, funext (Homeomorph.mul_apply f g)]
    exact hf.comp hg
  inv_mem' {f} hf := by
    rw [Set.mem_ofPred_eq, funext (Homeomorph.inv_apply f)]
    exact hf.symm

/-- Membership in the PL homeomorphism subgroup is precisely PL regularity of the underlying
map; its inverse is then automatically PL. -/
@[simp]
theorem mem_plHomeomorphSubgroup {s : PLStructure M n} {f : M ≃ₜ M} :
    f ∈ s.plHomeomorphSubgroup ↔ s.IsPLMap s f := Iff.rfl

section Transport

variable {N : Type u} [TopologicalSpace N] (s : PLStructure M n) (e : M ≃ₜ N)

/-- Transport of a PL structure carries its PL homeomorphism subgroup to the conjugate
subgroup. -/
theorem map_plHomeomorphSubgroup :
    s.plHomeomorphSubgroup.map (Homeomorph.homeoCongr e : (M ≃ₜ M) →* (N ≃ₜ N)) =
      (s.map e).plHomeomorphSubgroup := by
  ext f
  rw [Subgroup.map_equiv_eq_comap_symm, Subgroup.mem_comap, Homeomorph.homeoCongr_symm]
  simp [Function.comp_def, funext (Homeomorph.homeoCongr_apply_apply e.symm f)]

/-- A homeomorphism transporting a PL structure induces an isomorphism of its PL
homeomorphism groups, by conjugating representatives. -/
def plHomeomorphCongr : s.plHomeomorphSubgroup ≃* (s.map e).plHomeomorphSubgroup :=
  (Homeomorph.homeoCongr e).subgroupMap s.plHomeomorphSubgroup |>.trans
    (MulEquiv.subgroupCongr (s.map_plHomeomorphSubgroup e))

/-- The isomorphism of PL homeomorphism groups acts by conjugation on the underlying
homeomorphisms. -/
@[simp]
theorem coe_plHomeomorphCongr (f : s.plHomeomorphSubgroup) :
    (s.plHomeomorphCongr e f : N ≃ₜ N) = Homeomorph.homeoCongr e f := by
  simp only [plHomeomorphCongr, MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply,
    MulEquiv.coe_subgroupMap_apply]

/-- The inverse isomorphism of PL homeomorphism groups acts by conjugation by the inverse
homeomorphism. -/
@[simp]
theorem coe_plHomeomorphCongr_symm_apply (g : (s.map e).plHomeomorphSubgroup) :
    ((s.plHomeomorphCongr e).symm g : M ≃ₜ M) = Homeomorph.homeoCongr e.symm g := by
  simp [plHomeomorphCongr, MulEquiv.subgroupMap_symm_apply]

end Transport

end TauCeti.PLStructure
