/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GraphOfGroups.Path

/-!
# Change of base vertex for the fundamental group of a graph of groups

An `𝔸`-path `p` from `a` to `b` in a graph of groups `𝔸` conjugates closed paths at `a` into
closed paths at `b`, `q ↦ p⁻¹ q p`, and so gives an isomorphism
`π₁.mulEquivOfPath p : π₁(𝔸, a) ≃* π₁(𝔸, b)`. It depends only on the homotopy class of `p`, the
empty path gives the identity, concatenation of paths gives composition, and for a closed path
`p` it is the inner automorphism by `p⁻¹`. Over a preconnected graph any two vertices are joined
by an `𝔸`-path, so the fundamental groups at any two vertices are isomorphic.

The isomorphism is compatible with the embeddings of vertex groups: it sends the conjugate
`q g q⁻¹` of `g ∈ A_c` along a path `q` from `a` to `c` to the conjugate of `g` along `p⁻¹ q`.
The images of a subgroup of `A_c` along two paths from the same vertex are conjugate, so the
change of base vertex carries the image of any subgroup of a vertex group (the vertex group
itself, or an edge group image `α_e(A_e)` or `ω_e(A_e)`) to a conjugate of its image along any
chosen path from `b`. Read in `π₁(𝔸, T)`, the change of base vertex is conjugation by the inverse
of the image of `p`, `x ↦ p⁻¹ x p`.

## Main definitions

* `TauCeti.GraphOfGroups.π₁.mulEquivOfPath`: the isomorphism `π₁(𝔸, a) ≃* π₁(𝔸, b)` given by
  an `𝔸`-path from `a` to `b`.

## Main results

* `TauCeti.GraphOfGroups.π₁.mulEquivOfPath_comp`, `π₁.mulEquivOfPath_symm`,
  `π₁.mulEquivOfPath_congr`: change of base vertex is functorial in homotopy classes of paths.
* `TauCeti.GraphOfGroups.π₁.mulEquivOfPath_eq_conj`: along a closed path it is an inner
  automorphism.
* `TauCeti.GraphOfGroups.π₁.mulEquivOfPath_comp_vertexHom`, `π₁.mulEquivOfPath_vertexHom`: its
  effect on `π₁.vertexHom`.
* `TauCeti.GraphOfGroups.π₁.map_mulEquivOfPath_map_vertexHom`: it carries the image of a
  subgroup of a vertex group to a conjugate of its image.
* `TauCeti.GraphOfGroups.π₁.nonempty_mulEquiv_of_preconnected`: over a preconnected graph,
  `π₁(𝔸, a) ≃* π₁(𝔸, b)` for all vertices `a`, `b`.

## References

* J.-P. Serre, *Trees*, Chapter I, §5.1, Proposition 20.
* I. Kapovich, R. Weidmann, A. Myasnikov, *Foldings, graphs of groups and the membership problem*,
  Internat. J. Algebra Comput. 15 (2005), §2, Definitions 2.2–2.3.
-/

public section

universe u v w x

namespace TauCeti

namespace GraphOfGroups

variable {Γ : SerreGraph.{u, v}} {𝔸 : GraphOfGroups.{u, v, w, x} Γ}

namespace π₁

variable {a b c : Γ.V}

private def conjHom (p : 𝔸.Path ⟨a⟩ ⟨b⟩) : π₁ 𝔸 a →* π₁ 𝔸 b where
  toFun := lift (fun q ↦ mk ((p.reverse.comp q).comp p)) fun _ _ h ↦
    mk_eq_mk_iff.2 ((h.comp_left p.reverse).comp_right p)
  map_one' := by
    simpa [← mk_nil, mk_eq_mk_iff] using Path.Homotopic.reverse_comp p
  map_mul' x y := induction_on x fun q ↦ induction_on y fun r ↦ by
    rw [← mk_comp, lift_mk, lift_mk, lift_mk, ← mk_comp, mk_eq_mk_iff]
    -- `p⁻¹ q (p p⁻¹) r p ~ p⁻¹ q r p`.
    simpa only [Quiver.Path.comp_assoc, Quiver.Path.nil_comp] using
      ((Path.Homotopic.refl (p.reverse.comp q)).comp
        ((Path.Homotopic.comp_reverse p).comp (.refl (r.comp p)))).symm

private theorem conjHom_mk (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (q : 𝔸.Path ⟨a⟩ ⟨a⟩) :
    conjHom p (mk q) = mk ((p.reverse.comp q).comp p) :=
  lift_mk _ _ q

private theorem conjHom_comp (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (p' : 𝔸.Path ⟨b⟩ ⟨c⟩) (x : π₁ 𝔸 a) :
    conjHom (p.comp p') x = conjHom p' (conjHom p x) :=
  induction_on x fun q ↦ by simp [conjHom_mk, Quiver.Path.comp_assoc]

private theorem conjHom_nil (x : π₁ 𝔸 a) : conjHom Quiver.Path.nil x = x :=
  induction_on x fun q ↦ by simp [conjHom_mk]

private theorem conjHom_congr {p p' : 𝔸.Path ⟨a⟩ ⟨b⟩} (h : p.Homotopic p') (x : π₁ 𝔸 a) :
    conjHom p x = conjHom p' x :=
  induction_on x fun q ↦ by
    rw [conjHom_mk, conjHom_mk, mk_eq_mk_iff]
    exact (h.reverse.comp (.refl q)).comp h

private theorem conjHom_conjHom {p : 𝔸.Path ⟨a⟩ ⟨b⟩} {p' : 𝔸.Path ⟨b⟩ ⟨a⟩}
    (h : Path.Homotopic (p.comp p') .nil) (x : π₁ 𝔸 a) : conjHom p' (conjHom p x) = x := by
  rw [← conjHom_comp, conjHom_congr h, conjHom_nil]

/-- Change of base vertex: an `𝔸`-path `p` from `a` to `b` gives the isomorphism
`π₁(𝔸, a) ≃* π₁(𝔸, b)` sending the class of a closed path `q` at `a` to the class of `p⁻¹ q p`.
Its inverse is the change of base vertex along the reverse path. -/
def mulEquivOfPath (p : 𝔸.Path ⟨a⟩ ⟨b⟩) : π₁ 𝔸 a ≃* π₁ 𝔸 b :=
  MonoidHom.toMulEquiv (conjHom p) (conjHom p.reverse)
    (MonoidHom.ext (conjHom_conjHom (Path.Homotopic.comp_reverse p)))
    (MonoidHom.ext (conjHom_conjHom (Path.Homotopic.reverse_comp p)))

@[simp] theorem mulEquivOfPath_mk (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (q : 𝔸.Path ⟨a⟩ ⟨a⟩) :
    mulEquivOfPath p (mk q) = mk ((p.reverse.comp q).comp p) :=
  conjHom_mk p q

/-- The inverse of the change of base vertex along `p` is the change along `p⁻¹`. -/
theorem mulEquivOfPath_symm (p : 𝔸.Path ⟨a⟩ ⟨b⟩) :
    (mulEquivOfPath p).symm = mulEquivOfPath p.reverse :=
  MulEquiv.ext fun _ ↦ rfl

@[simp] theorem mulEquivOfPath_symm_mk (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (q : 𝔸.Path ⟨b⟩ ⟨b⟩) :
    (mulEquivOfPath p).symm (mk q) = mk ((p.comp q).comp p.reverse) := by
  simp [mulEquivOfPath_symm]

@[simp] theorem mulEquivOfPath_reverse_apply_apply (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (x : π₁ 𝔸 a) :
    mulEquivOfPath p.reverse (mulEquivOfPath p x) = x :=
  (mulEquivOfPath p).symm_apply_apply x

@[simp] theorem mulEquivOfPath_apply_reverse_apply (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (x : π₁ 𝔸 b) :
    mulEquivOfPath p (mulEquivOfPath p.reverse x) = x :=
  (mulEquivOfPath p).apply_symm_apply x

/-- The change of base vertex along the empty path is the identity. -/
@[simp] theorem mulEquivOfPath_nil :
    mulEquivOfPath (Quiver.Path.nil : 𝔸.Path ⟨a⟩ ⟨a⟩) = MulEquiv.refl (π₁ 𝔸 a) :=
  MulEquiv.ext conjHom_nil

/-- The change of base vertex along a concatenation is the composite of the changes. -/
theorem mulEquivOfPath_comp (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (p' : 𝔸.Path ⟨b⟩ ⟨c⟩) :
    mulEquivOfPath (p.comp p') = (mulEquivOfPath p).trans (mulEquivOfPath p') :=
  MulEquiv.ext (conjHom_comp p p')

/-- Homotopic paths give the same change of base vertex. -/
theorem mulEquivOfPath_congr {p p' : 𝔸.Path ⟨a⟩ ⟨b⟩} (h : p.Homotopic p') :
    mulEquivOfPath p = mulEquivOfPath p' :=
  MulEquiv.ext (conjHom_congr h)

/-- Along a closed path `s`, the change of base vertex is conjugation by `s⁻¹`. -/
theorem mulEquivOfPath_eq_conj (s : 𝔸.Path ⟨a⟩ ⟨a⟩) : mulEquivOfPath s = MulAut.conj (mk s)⁻¹ :=
  MulEquiv.ext fun x ↦ induction_on x fun q ↦ by
    simp [← mk_reverse, ← mk_comp]

/-- The change of base vertex along `p` sends the conjugate of `g ∈ A_c` along a path `q` to its
conjugate along `p⁻¹ q`. -/
@[simp] theorem mulEquivOfPath_vertexHom (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (q : 𝔸.Path ⟨a⟩ ⟨c⟩)
    (g : 𝔸.vertexGroup c) : mulEquivOfPath p (vertexHom q g) = vertexHom (p.reverse.comp q) g := by
  simp only [vertexHom_apply, mulEquivOfPath_mk, Quiver.Path.reverse_comp,
    Quiver.Path.reverse_reverse, Quiver.Path.comp_assoc]

@[simp] theorem mulEquivOfPath_comp_vertexHom (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (q : 𝔸.Path ⟨a⟩ ⟨c⟩) :
    (mulEquivOfPath p : π₁ 𝔸 a →* π₁ 𝔸 b).comp (vertexHom q) = vertexHom (p.reverse.comp q) :=
  MonoidHom.ext (mulEquivOfPath_vertexHom p q)

/-- The inverse of the change of base vertex along `p` sends the conjugate of `g ∈ A_c` along a
path `q` from `b` to its conjugate along `p q`. -/
@[simp] theorem mulEquivOfPath_symm_vertexHom (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (q : 𝔸.Path ⟨b⟩ ⟨c⟩)
    (g : 𝔸.vertexGroup c) : (mulEquivOfPath p).symm (vertexHom q g) = vertexHom (p.comp q) g := by
  simp [mulEquivOfPath_symm]

@[simp] theorem mulEquivOfPath_symm_comp_vertexHom (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (q : 𝔸.Path ⟨b⟩ ⟨c⟩) :
    ((mulEquivOfPath p).symm : π₁ 𝔸 b →* π₁ 𝔸 a).comp (vertexHom q) = vertexHom (p.comp q) :=
  MonoidHom.ext (mulEquivOfPath_symm_vertexHom p q)

/-- The change of base vertex along `p` carries the image of a subgroup `H` of a vertex group
`A_c` along a path `q` from `a` to a conjugate of its image along any path `r` from `b`: the
conjugate by the class of `p⁻¹ q r⁻¹`. With `H = ⊤` this is the image of the vertex group, and
with `H` the image of an edge group under `α_e` or `ω_e` it is an edge group image. -/
theorem map_mulEquivOfPath_map_vertexHom (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (q : 𝔸.Path ⟨a⟩ ⟨c⟩)
    (r : 𝔸.Path ⟨b⟩ ⟨c⟩) (H : Subgroup (𝔸.vertexGroup c)) :
    (H.map (vertexHom q)).map (mulEquivOfPath p : π₁ 𝔸 a →* π₁ 𝔸 b) =
      (H.map (vertexHom r)).map
        (MulAut.conj (mk ((p.reverse.comp q).comp r.reverse)) : π₁ 𝔸 b →* π₁ 𝔸 b) := by
  rw [Subgroup.map_map, mulEquivOfPath_comp_vertexHom, map_vertexHom_eq_map_conj r]

/-- Reading letters in `π₁(𝔸, T)` turns the change of base vertex along `p` into conjugation by
the inverse of the image of `p`, `x ↦ p⁻¹ x p`. -/
@[simp] theorem toπ₁Tree_mulEquivOfPath (T : Set Γ.E) (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (x : π₁ 𝔸 a) :
    toπ₁Tree 𝔸 b T (mulEquivOfPath p x) = (p.toπ₁Tree T)⁻¹ * toπ₁Tree 𝔸 a T x * p.toπ₁Tree T :=
  induction_on x fun q ↦ by simp [mul_assoc]

/-- Reading letters in `π₁(𝔸, T)` turns the inverse of the change of base vertex along `p` into
conjugation by the image of `p`, `x ↦ p x p⁻¹`. -/
@[simp] theorem toπ₁Tree_mulEquivOfPath_symm (T : Set Γ.E) (p : 𝔸.Path ⟨a⟩ ⟨b⟩) (x : π₁ 𝔸 b) :
    toπ₁Tree 𝔸 a T ((mulEquivOfPath p).symm x) =
      p.toπ₁Tree T * toπ₁Tree 𝔸 b T x * (p.toπ₁Tree T)⁻¹ := by
  simp [mulEquivOfPath_symm]

end π₁

variable (𝔸) in
/-- Over a preconnected graph the fundamental groups of a graph of groups at any two vertices are
isomorphic. -/
theorem π₁.nonempty_mulEquiv_of_preconnected (hΓ : Γ.Preconnected) (a b : Γ.V) :
    Nonempty (π₁ 𝔸 a ≃* π₁ 𝔸 b) :=
  (Path.nonempty_of_preconnected 𝔸 hΓ a b).map π₁.mulEquivOfPath

end GraphOfGroups

end TauCeti
