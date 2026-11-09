/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Algebra
public import Mathlib.Topology.Algebra.ContinuousMonoidHom

/-!
# Mapping spaces into topological groups

For a pointed space `(X, x)` and a topological group `G`, the compact-open mapping space
`C(X, G)` is homeomorphic to the product of `G` with the based mapping space
`{f : C(X, G) // f x = 1}`. The homeomorphism sends `(g, f)` to `g * f`; its inverse sends
`f` to `(f x, (f x)⁻¹ * f)`. Thus evaluation at `x` is the projection of a trivial product,
and constant maps give its canonical section. No compactness or separation hypothesis is
needed on either space.

For sphere sources this identifies free sphere maps into a topological group with a group
coordinate and a based sphere map. The construction uses left multiplication, so it also
applies to noncommutative groups.

## Main declarations

* `TauCeti.mappingSpaceGroupHomeomorph`: `G × {f : C(X, G) // f x = 1} ≃ₜ C(X, G)`, with its
  action `_apply` and the coordinates `_symm_fst`, `_symm_snd_val` of its inverse.
* `TauCeti.mappingSpaceGroupHomeomorph_symm_comp`,
  `TauCeti.mappingSpaceGroupHomeomorph_symm_postcomp`: naturality under precomposition by a
  pointed map and under postcomposition by a continuous group homomorphism.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.
-/

public section

open ContinuousMap

namespace TauCeti

variable {X G : Type*} [TopologicalSpace X] [TopologicalSpace G]
  [Group G] [IsTopologicalGroup G]

/-- The product decomposition of maps into a topological group: multiply a based map on
the left by a constant. The inverse records the value at the basepoint and translates the
map to take the value `1` there. -/
def mappingSpaceGroupHomeomorph (x : X) :
    G × {f : C(X, G) // f x = 1} ≃ₜ C(X, G) where
  toFun p := ContinuousMap.const X p.1 * p.2.val
  invFun f := (f x, ⟨ContinuousMap.const X (f x)⁻¹ * f, by simp⟩)
  left_inv p := by ext <;> simp [p.2.property]
  right_inv f := by ext; simp
  continuous_toFun :=
    (continuous_postcomp ⟨fun p : G × G ↦ p.1 * p.2, continuous_mul⟩).comp
      (continuous_prodMk_const.comp (continuous_fst.prodMk continuous_snd.subtype_val))
  continuous_invFun :=
    (continuous_eval_const x).prodMk
      (((continuous_postcomp ⟨fun p : G × G ↦ p.1 * p.2, continuous_mul⟩).comp
        (continuous_prodMk_const.comp
          ((continuous_eval_const x).inv.prodMk continuous_id))).subtype_mk (fun f ↦ by simp))

/-- The decomposition sends `(g, f)` to the product of the constant map `g` and `f`. -/
@[simp]
theorem mappingSpaceGroupHomeomorph_apply (x : X)
    (p : G × {f : C(X, G) // f x = 1}) :
    mappingSpaceGroupHomeomorph x p = ContinuousMap.const X p.1 * p.2.val :=
  (rfl)

/-- The group coordinate of the decomposition of `f` is its value at the basepoint. -/
@[simp]
theorem mappingSpaceGroupHomeomorph_symm_fst (x : X) (f : C(X, G)) :
    ((mappingSpaceGroupHomeomorph x).symm f).1 = f x :=
  (rfl)

/-- The based coordinate of the decomposition of `f` is the translate `(f x)⁻¹ * f`. -/
@[simp]
theorem mappingSpaceGroupHomeomorph_symm_snd_val (x : X) (f : C(X, G)) :
    ((mappingSpaceGroupHomeomorph x).symm f).2.val =
      ContinuousMap.const X (f x)⁻¹ * f :=
  (rfl)

variable {Y H : Type*} [TopologicalSpace Y] [TopologicalSpace H]
  [Group H] [IsTopologicalGroup H]

/-- The product decomposition is natural under precomposition by a pointed continuous map. -/
theorem mappingSpaceGroupHomeomorph_symm_comp (x : X) (y : Y) (h : C(Y, X))
    (hh : h y = x) (f : C(X, G)) :
    (mappingSpaceGroupHomeomorph y).symm (f.comp h) =
      (f x, ⟨((mappingSpaceGroupHomeomorph x).symm f).2.val.comp h, by simp [hh]⟩) := by
  ext <;> simp [hh]

/-- The product decomposition is natural under postcomposition by a continuous group
homomorphism, including for noncommutative groups. -/
theorem mappingSpaceGroupHomeomorph_symm_postcomp (x : X) (φ : G →ₜ* H) (f : C(X, G)) :
    (mappingSpaceGroupHomeomorph x).symm (φ.toContinuousMap.comp f) =
      (φ (f x), ⟨φ.toContinuousMap.comp ((mappingSpaceGroupHomeomorph x).symm f).2.val,
        by simp⟩) := by
  ext <;> simp

end TauCeti
