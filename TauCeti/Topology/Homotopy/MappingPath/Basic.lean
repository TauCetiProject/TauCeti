/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Homotopy.Equiv
public import Mathlib.Topology.Path

/-!
# Mapping-path replacements

The mapping-path space of `f : C(B, K)` consists of a point of `B` and a path starting
at its image. It has the subspace topology from `B × C(I, K)`, with the compact-open
topology on paths. Constant paths include `B` into this replacement; shrinking the
path by `γ(t) ↦ γ(s * t)` gives a strong deformation back to that inclusion.

Commutative squares act on replacements, compatibly with the source projection,
endpoint and shrinking homotopy. These constructions require no separation or
local compactness assumptions on `B` or `K`: only the interval is used as an
exponentiable domain. The endpoint-fibre comparisons are developed separately.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.7.
-/

public section

open unitInterval

universe u v u' v' u'' v''

namespace TauCeti

variable {B : Type u} {K : Type v} [TopologicalSpace B] [TopologicalSpace K]

/-- The mapping-path replacement, with its product/subspace compact-open topology. -/
abbrev MappingPathSpace (f : C(B, K)) :=
  {p : B × C(I, K) // p.2 0 = f p.1}

namespace MappingPathSpace

variable (f : C(B, K))

/-- Forget the path in a mapping-path replacement. -/
def proj : C(MappingPathSpace f, B) :=
  ⟨fun p ↦ p.val.1, by fun_prop⟩

@[simp]
theorem proj_apply (p : MappingPathSpace f) : proj f p = p.val.1 := (rfl)

/-- Evaluate a replacement path at its final endpoint. -/
def endpoint : C(MappingPathSpace f, K) :=
  ⟨fun p ↦ p.val.2 1, by fun_prop⟩

@[simp]
theorem endpoint_apply (p : MappingPathSpace f) : endpoint f p = p.val.2 1 := (rfl)

/-- Include the source using constant paths. -/
def incl : C(B, MappingPathSpace f) :=
  ⟨fun b ↦ ⟨(b, ContinuousMap.const I (f b)), rfl⟩,
    (continuous_id.prodMk (ContinuousMap.continuous_const'.comp f.continuous)).subtype_mk _⟩

@[simp]
theorem incl_val (b : B) : (incl f b).val = (b, ContinuousMap.const I (f b)) := (rfl)

@[simp]
theorem proj_comp_incl : (proj f).comp (incl f) = ContinuousMap.id B := by
  ext
  rfl

@[simp]
theorem endpoint_comp_incl : (endpoint f).comp (incl f) = f := by
  ext
  rfl

/-- Shrink a path toward its starting point, keeping the source coordinate fixed. -/
def shrinkHomotopy :
    ContinuousMap.Homotopy ((incl f).comp (proj f)) (ContinuousMap.id _) where
  toFun q := ⟨(q.2.val.1, ⟨fun t ↦ q.2.val.2 (q.1 * t),
    q.2.val.2.continuous.comp
      ((continuous_const.mul continuous_subtype_val).subtype_mk _)⟩), by
    simpa using q.2.property⟩
  continuous_toFun := by
    refine (continuous_snd.subtype_val.fst.prodMk ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact ((continuous_snd.comp continuous_fst).subtype_val.snd).eval
      (((continuous_fst.comp continuous_fst).subtype_val.mul
        continuous_snd.subtype_val).subtype_mk _)
  map_zero_left p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext t
      simpa using p.property
  map_one_left p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · ext t
      simp

@[simp]
theorem shrinkHomotopy_point (s : I) (p : MappingPathSpace f) :
    (shrinkHomotopy f (s, p)).val.1 = p.val.1 := (rfl)

@[simp]
theorem shrinkHomotopy_path (s t : I) (p : MappingPathSpace f) :
    (shrinkHomotopy f (s, p)).val.2 t = p.val.2 (s * t) := (rfl)

/-- The shrinking homotopy fixes every constant-path inclusion throughout. -/
@[simp]
theorem shrinkHomotopy_incl (s : I) (b : B) :
    shrinkHomotopy f (s, incl f b) = incl f b := by
  apply Subtype.ext
  apply Prod.ext rfl
  ext
  rfl

/-- The constant-path inclusion is a homotopy equivalence, inverse to projection. -/
def homotopyEquiv : ContinuousMap.HomotopyEquiv B (MappingPathSpace f) where
  toFun := incl f
  invFun := proj f
  left_inv := by rw [proj_comp_incl]
  right_inv := ⟨shrinkHomotopy f⟩

@[simp]
theorem homotopyEquiv_apply (b : B) : homotopyEquiv f b = incl f b := (rfl)

@[simp]
theorem homotopyEquiv_symm_apply (p : MappingPathSpace f) :
    (homotopyEquiv f).symm p = proj f p := (rfl)

variable {f}
variable {B' : Type u'} {K' : Type v'} [TopologicalSpace B'] [TopologicalSpace K']
  {f' : C(B', K')}

/-- A commutative square sends a replacement point to its image and postcomposes its path. -/
def map (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a) :
    C(MappingPathSpace f, MappingPathSpace f') := by
  refine ⟨fun p ↦ ⟨(a p.val.1, b.comp p.val.2), ?_⟩, ?_⟩
  · exact (congrArg b p.property).trans (ContinuousMap.congr_fun h p.val.1)
  · exact ((a.continuous.comp (proj f).continuous).prodMk
      ((ContinuousMap.continuous_postcomp b).comp
        continuous_subtype_val.snd)).subtype_mk _

@[simp]
theorem map_val (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a)
    (p : MappingPathSpace f) :
    (map a b h p).val = (a p.val.1, b.comp p.val.2) := (rfl)

/-- Projection is natural in a commutative square. -/
@[simp]
theorem proj_comp_map (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a) :
    (proj f').comp (map a b h) = a.comp (proj f) := by
  ext
  rfl

/-- Endpoint evaluation is natural in a commutative square. -/
@[simp]
theorem endpoint_comp_map (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a) :
    (endpoint f').comp (map a b h) = b.comp (endpoint f) := by
  ext
  rfl

/-- The constant-path inclusion is natural in a commutative square. -/
@[simp]
theorem map_comp_incl (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a) :
    (map a b h).comp (incl f) = (incl f').comp a := by
  apply ContinuousMap.ext
  intro x
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · ext t
    exact ContinuousMap.congr_fun h x

@[simp]
theorem map_id : map (ContinuousMap.id B) (ContinuousMap.id K) (by simp) =
    ContinuousMap.id (MappingPathSpace f) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  simp

variable {B'' : Type u''} {K'' : Type v''} [TopologicalSpace B''] [TopologicalSpace K'']
  {f'' : C(B'', K'')}

/-- Mapping-path replacements preserve composition of commutative squares. -/
theorem map_comp (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a)
    (a' : C(B', B'')) (b' : C(K', K'')) (h' : b'.comp f' = f''.comp a') :
    (map a' b' h').comp (map a b h) =
      map (a'.comp a) (b'.comp b) (by
        apply ContinuousMap.ext
        intro x
        exact (congrArg b' (ContinuousMap.congr_fun h x)).trans
          (ContinuousMap.congr_fun h' (a x))) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  rfl

/-- Shrinking commutes with the map induced by a commutative square. -/
@[simp]
theorem map_shrinkHomotopy (a : C(B, B')) (b : C(K, K'))
    (h : b.comp f = f'.comp a) (s : I) (p : MappingPathSpace f) :
    map a b h (shrinkHomotopy f (s, p)) =
      shrinkHomotopy f' (s, map a b h p) := by
  apply Subtype.ext
  rfl

end MappingPathSpace

end TauCeti
