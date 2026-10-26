/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.MappingPath.Fiber

/-!
# Functoriality of mapping-path fibres

A commutative square, together with a map of the chosen endpoints, induces a continuous map
of mapping-path fibres. It sends the source point along the top of the square and postcomposes
the path along the bottom. These maps preserve identities and composition and agree with the
maps of mapping-path replacements under the literal endpoint-fibre comparison.

A homotopy of commutative squares fixing the chosen target endpoint induces a homotopy of
these fibre maps, continuous jointly in the homotopy parameter and the entire fibre. Thus the
construction retains homotopies of maps, not just their action on separate paths. No
nonemptiness or separation assumption is needed.

For constant maps from a point, the comparison with native path spaces intertwines these maps
with postcomposition of paths.

## References

* G. W. Whitehead, *Elements of Homotopy Theory*, Chapter I.7.
-/

public section

open unitInterval

universe u v u' v' u'' v''

namespace TauCeti
namespace MappingPathFiber

variable {B : Type u} {K : Type v} [TopologicalSpace B] [TopologicalSpace K]
variable {B' : Type u'} {K' : Type v'} [TopologicalSpace B'] [TopologicalSpace K']
variable {B'' : Type u''} {K'' : Type v''} [TopologicalSpace B''] [TopologicalSpace K'']
variable {f : C(B, K)} {f' : C(B', K')} {f'' : C(B'', K'')}
variable {k : K} {k' : K'} {k'' : K''}

/-- A commutative square carrying `k` to `k'` acts on mapping-path fibres by applying the
source map and postcomposing the path. -/
def map (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a) (hk : b k = k') :
    C(MappingPathFiber f k, MappingPathFiber f' k') :=
  ⟨fun p ↦ ⟨(a p.val.1, b.comp p.val.2),
    (congrArg b p.property.1).trans (ContinuousMap.congr_fun h p.val.1),
    (congrArg b p.property.2).trans hk⟩,
    ((a.continuous.comp continuous_subtype_val.fst).prodMk
      ((ContinuousMap.continuous_postcomp b).comp continuous_subtype_val.snd)).subtype_mk _⟩

@[simp]
theorem map_val (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a)
    (hk : b k = k') (p : MappingPathFiber f k) :
    (map a b h hk p).val = (a p.val.1, b.comp p.val.2) := (rfl)

/-- The source projection is natural in commutative squares. -/
@[simp]
theorem proj_comp_map (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a)
    (hk : b k = k') :
    (proj f' k').comp (map a b h hk) = a.comp (proj f k) := by
  apply ContinuousMap.ext
  intro p
  simp

/-- The literal endpoint-fibre comparison commutes with maps of replacements. -/
@[simp]
theorem endpointHomeomorph_map (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a)
    (hk : b k = k') (p : MappingPathFiber f k) :
    (endpointHomeomorph f' k' (map a b h hk p)).val =
      MappingPathSpace.map a b h (endpointHomeomorph f k p).val := by
  apply Subtype.ext
  simp

/-- The pullback comparison respects the induced map of fixed-end path spaces. -/
@[simp]
theorem pullbackHomeomorph_map_val (a : C(B, B')) (b : C(K, K'))
    (h : b.comp f = f'.comp a) (hk : b k = k') (p : MappingPathFiber f k) :
    (pullbackHomeomorph f' k' (map a b h hk p)).val =
      (a p.val.1, map b b (by simp) hk (pullbackHomeomorph f k p).val.2) := by
  apply Prod.ext
  · simp
  · apply Subtype.ext
    simp only [pullbackHomeomorph_val_snd_val, map_val]
    exact Prod.ext (ContinuousMap.congr_fun h p.val.1).symm rfl

/-- The identity commutative square induces the identity map on the mapping-path fibre. -/
@[simp]
theorem map_id : map (f := f) (f' := f) (k := k) (k' := k) (.id B) (.id K) (by simp) rfl =
    ContinuousMap.id (MappingPathFiber f k) := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  exact Prod.ext rfl (ContinuousMap.id_comp _)

/-- Mapping-path fibres preserve composition of endpoint-preserving commutative squares. -/
theorem map_comp (a : C(B, B')) (b : C(K, K')) (h : b.comp f = f'.comp a)
    (hk : b k = k') (a' : C(B', B'')) (b' : C(K', K''))
    (h' : b'.comp f' = f''.comp a') (hk' : b' k' = k'') :
    (map a' b' h' hk').comp (map a b h hk) =
      map (a'.comp a) (b'.comp b) (by
        ext x
        exact (congrArg b' (ContinuousMap.congr_fun h x)).trans
          (ContinuousMap.congr_fun h' (a x))) ((congrArg b' hk).trans hk') := by
  apply ContinuousMap.ext
  intro p
  apply Subtype.ext
  simp

section Homotopy

variable {a₀ a₁ : C(B, B')} {b₀ b₁ : C(K, K')}
variable (A : a₀.Homotopy a₁) (H : b₀.Homotopy b₁)
variable (hs : ∀ t x, H (t, f x) = f' (A (t, x))) (hk : ∀ t, H (t, k) = k')

/-- A continuous homotopy of commutative squares fixing the endpoint induces a homotopy of
mapping-path fibre maps. The path at time `t` is postcomposed with the time-`t` target map. -/
def mapHomotopy :
    ContinuousMap.Homotopy
      (map (f := f) (f' := f') (k := k) (k' := k') a₀ b₀
        (ContinuousMap.ext fun x ↦ by simpa using hs 0 x)
        (by simpa using hk 0))
      (map (f := f) (f' := f') (k := k) (k' := k') a₁ b₁
        (ContinuousMap.ext fun x ↦ by simpa using hs 1 x)
        (by simpa using hk 1)) where
  toFun q := ⟨(A (q.1, q.2.val.1),
    ⟨fun t ↦ H (q.1, q.2.val.2 t), by fun_prop⟩),
    by simpa only [ContinuousMap.coe_mk, q.2.property.1] using hs q.1 q.2.val.1,
    by simpa only [ContinuousMap.coe_mk, q.2.property.2] using hk q.1⟩
  continuous_toFun := by
    refine ((A.continuous.comp (continuous_fst.prodMk continuous_snd.subtype_val.fst)).prodMk
      ?_).subtype_mk _
    apply ContinuousMap.continuous_of_continuous_uncurry
    exact H.continuous.comp ((continuous_fst.comp continuous_fst).prodMk
      (((continuous_snd.comp continuous_fst).subtype_val.snd).eval continuous_snd))
  map_zero_left p := by
    apply Subtype.ext
    apply Prod.ext
    · exact A.apply_zero _
    · ext t
      exact H.apply_zero _
  map_one_left p := by
    apply Subtype.ext
    apply Prod.ext
    · exact A.apply_one _
    · ext t
      exact H.apply_one _

@[simp]
theorem mapHomotopy_val (s : I) (p : MappingPathFiber f k) :
    (mapHomotopy A H hs hk (s, p)).val =
      (A (s, p.val.1), ⟨fun t ↦ H (s, p.val.2 t), by fun_prop⟩) := (rfl)

/-- The induced homotopy lies over the supplied homotopy of source maps. -/
theorem proj_mapHomotopy (s : I) (p : MappingPathFiber f k) :
    proj f' k' (mapHomotopy A H hs hk (s, p)) = A (s, proj f k p) := by
  simp

end Homotopy

end MappingPathFiber

variable {K : Type v} {K' : Type v'} [TopologicalSpace K] [TopologicalSpace K']

/-- For constant maps from a point, the path-space comparison intertwines maps of fibres
with the native postcomposition of paths. -/
@[simp]
theorem mappingPathFiberConstHomeomorphPath_map (b : C(K, K')) (x k : K)
    (p : MappingPathFiber (ContinuousMap.const Unit x) k) :
    mappingPathFiberConstHomeomorphPath (b x) (b k)
      (MappingPathFiber.map (.id Unit) b (by ext; rfl) rfl p) =
      (mappingPathFiberConstHomeomorphPath x k p).map b.continuous := by
  ext t
  simp

end TauCeti
