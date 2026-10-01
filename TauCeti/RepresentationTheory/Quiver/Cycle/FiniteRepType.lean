/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.Indecomposable
public import TauCeti.RepresentationTheory.Quiver.Cycle.Basic
public import TauCeti.RepresentationTheory.Quiver.FiniteRepType.Basic
public import TauCeti.RepresentationTheory.Quiver.Representation.DimensionVector
public import TauCeti.RingTheory.AdjoinRoot.Basic
public import TauCeti.RingTheory.Polynomial.Truncated

/-!
# The cycle quiver has infinite representation type

A representation of the cycle quiver `TauCeti.Quiver.Cycle n` on `n + 2` vertices is a vector
space at each vertex together with a map to the next one, cyclically. This file builds the family
of *nilpotent* ones: the truncated polynomial algebra `k[X]/(Xᵐ⁺¹)` at every vertex, with the
arrow that closes the cycle acting by multiplication by `X` and every other arrow by the identity
(`TauCeti.cycleNilpotentRep`).

An endomorphism of such a representation is *constant along the cycle*: naturality along an arrow
whose action is the identity says that its components at the two ends agree, and
`TauCeti.Quiver.Cycle.induction_of_ne_last` walks that equality from the first vertex to every
other one. Naturality along the one remaining arrow then says that the common value commutes with
multiplication by `X`, so it is multiplication by its own value at `1`
(`TauCeti.AdjoinRoot.eq_mulRight_of_root_mul`). Thus the endomorphism algebra is recorded
faithfully in `k[X]/(Xᵐ⁺¹)`, a local ring
(`TauCeti.isLocalRing_adjoinRoot_X_pow`), and each of these representations is indecomposable.
Their dimension vectors are the constant `m + 1`, so distinct sizes give non-isomorphic
representations, and the cycle quiver has infinite representation type over **every** field.

This is the `Ã` obstruction of the non-Dynkin half of Gabriel's theorem, one step beyond the loop
(`TauCeti.not_isFiniteRepType_oneLoop`, the case of a single vertex) and the two parallel arrows of
the Kronecker quiver (`TauCeti.not_isFiniteRepType_kronecker`). Its consequence for an arbitrary
quiver -- that a quiver of finite representation type has no oriented cycle through distinct
vertices -- is drawn in `TauCeti.RepresentationTheory.Quiver.FiniteRepType.Obstructions`.

## Main definitions

* `TauCeti.cycleNilpotentWeight`: the element of `k[X]/(Xᵐ⁺¹)` by which the arrow out of a vertex
  acts, the root on the closing arrow and `1` elsewhere.
* `TauCeti.cycleNilpotentRep`: the nilpotent representation of size `m + 1` built from it.

## Main results

* `TauCeti.indecomposable_cycleNilpotentRep`: the nilpotent representations are indecomposable.
* `TauCeti.dimVector_cycleNilpotentRep`: their dimension vector is the constant `m + 1`.
* `TauCeti.nonempty_cycleNilpotentRep_iso_iff`: two of them are isomorphic exactly when their
  sizes agree.
* `TauCeti.not_isFiniteRepType_cycle`: **over every field the cycle quiver has infinite
  representation type.**

## Implementation notes

All the arrows act by multiplication by an element of `k[X]/(Xᵐ⁺¹)`, recorded by
`TauCeti.cycleNilpotentWeight`, rather than the closing arrow acting by multiplication and the
others by the identity: with one uniform shape the representation is a single application of
`CategoryTheory.Paths.lift`.

`TauCeti.cycleNilpotentRep` carries `@[expose]` for the same reason as
`TauCeti.oneLoopNilpotentRep`: a functor built by `CategoryTheory.Paths.lift` records its value on
objects only in its definition, so the vertex spaces are visible as `k[X]/(Xᵐ⁺¹)` only once the
body is exposed. The components of an endomorphism at the vertices of the cycle are collected by
the private `cycleApp`.

## References

* I. Assem, D. Simson, A. Skowroński, *Elements of the Representation Theory of Associative
  Algebras*, Volume I, Chapter VII.
* H. Derksen, J. Weyman, *An Introduction to Quiver Representations*, Chapter 4.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

variable (k : Type u) [Field k] (n m : ℕ)

/-- **The weight of the arrow out of a vertex** in the nilpotent representation
`TauCeti.cycleNilpotentRep`: the root of `Xᵐ⁺¹` on the arrow that closes the cycle, and `1` on
every other arrow. -/
noncomputable def cycleNilpotentWeight (i : Quiver.Cycle n) : AdjoinRoot ((X : k[X]) ^ (m + 1)) :=
  if i = Quiver.Cycle.last then AdjoinRoot.root ((X : k[X]) ^ (m + 1)) else 1

@[simp]
theorem cycleNilpotentWeight_last :
    cycleNilpotentWeight k n m Quiver.Cycle.last = AdjoinRoot.root ((X : k[X]) ^ (m + 1)) :=
  ite_eq_left rfl

/-- Every arrow but the closing one has weight `1`. -/
@[simp]
theorem cycleNilpotentWeight_of_ne_last {i : Quiver.Cycle n} (h : i ≠ Quiver.Cycle.last) :
    cycleNilpotentWeight k n m i = 1 :=
  ite_eq_right h

/-- **The nilpotent representation of the cycle quiver of size `m + 1`**: the truncated polynomial
algebra `k[X]/(Xᵐ⁺¹)` at every vertex, with each arrow acting by multiplication by its weight
`TauCeti.cycleNilpotentWeight`, so that the closing arrow multiplies by `X` and every other arrow
is the identity. -/
@[expose]
noncomputable def cycleNilpotentRep : QuiverRep.{u, 0, 0, u} k (Quiver.Cycle n) :=
  Paths.lift
    { obj := fun _ ↦ ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (m + 1)))
      map := fun {i _} _ ↦ ModuleCat.ofHom (LinearMap.mulLeft k (cycleNilpotentWeight k n m i)) }

variable {k n m}

/-- Every vertex space of `TauCeti.cycleNilpotentRep` is `k[X]/(Xᵐ⁺¹)`. -/
@[simp]
theorem cycleNilpotentRep_obj (v : Paths (Quiver.Cycle n)) :
    (cycleNilpotentRep k n m).obj v = ModuleCat.of k (AdjoinRoot ((X : k[X]) ^ (m + 1))) :=
  rfl

/-- The arrow out of a vertex acts on `TauCeti.cycleNilpotentRep` by multiplication by its
weight. -/
theorem cycleNilpotentRep_map_arrow (i : Quiver.Cycle n) :
    (cycleNilpotentRep k n m).map (Quiver.Hom.toPath (Quiver.Cycle.arrow i)) =
      ModuleCat.ofHom (LinearMap.mulLeft k (cycleNilpotentWeight k n m i)) :=
  Paths.lift_toPath _ _

/-- The action of an arrow, read on an element of the vertex space. -/
@[simp]
theorem cycleNilpotentRep_map_arrow_apply (i : Quiver.Cycle n)
    (x : AdjoinRoot ((X : k[X]) ^ (m + 1))) :
    ((cycleNilpotentRep k n m).map (Quiver.Hom.toPath (Quiver.Cycle.arrow i))).hom x =
      cycleNilpotentWeight k n m i * x := by
  rw [cycleNilpotentRep_map_arrow]
  rfl

/-- The component at a vertex of an endomorphism of a nilpotent cycle representation, as a linear
map on `k[X]/(Xᵐ⁺¹)`. -/
private noncomputable def cycleApp
    (f : cycleNilpotentRep k n m ⟶ cycleNilpotentRep k n m) (i : Quiver.Cycle n) :
    AdjoinRoot ((X : k[X]) ^ (m + 1)) →ₗ[k] AdjoinRoot ((X : k[X]) ^ (m + 1)) :=
  (f.app (i : Paths (Quiver.Cycle n))).hom

-- Rewriting with this lemma, rather than unfolding `cycleApp`, is what keeps the passage from a
-- vertex to the corresponding object of `CategoryTheory.Paths` named as `Paths.of`, where the
-- `CategoryTheory.NatTrans` lemmas can still see it.
/-- The component at a vertex is the value of the natural transformation at the image of that
vertex under the embedding `CategoryTheory.Paths.of` of the quiver in its path category. -/
private theorem cycleApp_def (f : cycleNilpotentRep k n m ⟶ cycleNilpotentRep k n m)
    (i : Quiver.Cycle n) :
    cycleApp f i = (f.app ((Paths.of (Quiver.Cycle n)).obj i)).hom := (rfl)

/-- An endomorphism is determined by its components. -/
private theorem cycleNilpotentRep_hom_ext
    {f g : cycleNilpotentRep k n m ⟶ cycleNilpotentRep k n m}
    (h : ∀ i : Quiver.Cycle n, cycleApp f i = cycleApp g i) : f = g := by
  apply NatTrans.ext
  funext v
  exact ModuleCat.hom_ext (h v)

-- Each of the three identities below closes with a `rfl` that only reconciles the `k`-module
-- instances carried by `ModuleCat.of k (AdjoinRoot (Xᵐ⁺¹))` with those on `AdjoinRoot (Xᵐ⁺¹)`
-- itself; the two sides are otherwise identical.
/-- Every component of the zero endomorphism is zero. -/
private theorem cycleApp_zero (i : Quiver.Cycle n) :
    cycleApp (0 : cycleNilpotentRep k n m ⟶ cycleNilpotentRep k n m) i = 0 := by
  rw [cycleApp_def, NatTrans.app_zero, ModuleCat.hom_zero]
  rfl

/-- Every component of the identity endomorphism is the identity. -/
private theorem cycleApp_id (i : Quiver.Cycle n) :
    cycleApp (𝟙 (cycleNilpotentRep k n m)) i = LinearMap.id := by
  rw [cycleApp_def, NatTrans.id_app, ModuleCat.hom_id]
  rfl

/-- The components of a composite of endomorphisms are the composites of their components. -/
private theorem cycleApp_comp (f g : cycleNilpotentRep k n m ⟶ cycleNilpotentRep k n m)
    (i : Quiver.Cycle n) : cycleApp (f ≫ g) i = (cycleApp g i).comp (cycleApp f i) := by
  rw [cycleApp_def, cycleApp_def, cycleApp_def, NatTrans.comp_app, ModuleCat.hom_comp]
  rfl

/-- **Naturality along the arrow out of a vertex**: the component at the head of the arrow
intertwines multiplication by the weight with the component at its tail. -/
private theorem cycleApp_weight_mul (f : cycleNilpotentRep k n m ⟶ cycleNilpotentRep k n m)
    (i : Quiver.Cycle n) (x : AdjoinRoot ((X : k[X]) ^ (m + 1))) :
    cycleApp f i.succ (cycleNilpotentWeight k n m i * x) =
      cycleNilpotentWeight k n m i * cycleApp f i x := by
  have hnat : cycleApp f i.succ
        (((cycleNilpotentRep k n m).map (Quiver.Hom.toPath (Quiver.Cycle.arrow i))).hom x) =
      ((cycleNilpotentRep k n m).map (Quiver.Hom.toPath (Quiver.Cycle.arrow i))).hom
        (cycleApp f i x) :=
    congrArg (fun g ↦ (ModuleCat.Hom.hom g) x)
      (f.naturality (Quiver.Hom.toPath (Quiver.Cycle.arrow i)))
  rw [cycleNilpotentRep_map_arrow_apply, cycleNilpotentRep_map_arrow_apply] at hnat
  exact hnat

/-- **An endomorphism of a nilpotent cycle representation is constant along the cycle.** All the
arrows but the closing one act by the identity, so naturality identifies consecutive components,
and `TauCeti.Quiver.Cycle.induction_of_ne_last` propagates the identification from the first
vertex to every other one. -/
private theorem cycleApp_eq_first (f : cycleNilpotentRep k n m ⟶ cycleNilpotentRep k n m)
    (i : Quiver.Cycle n) : cycleApp f i = cycleApp f Quiver.Cycle.first := by
  refine Quiver.Cycle.induction_of_ne_last
    (P := fun j ↦ cycleApp f j = cycleApp f Quiver.Cycle.first) rfl (fun j hj hji ↦ ?_) i
  refine LinearMap.ext fun x ↦ ?_
  have hx := cycleApp_weight_mul f j x
  rw [cycleNilpotentWeight_of_ne_last k n m hj, one_mul, one_mul] at hx
  rw [hx, hji]

/-- Naturality along the closing arrow: the common component commutes with multiplication by the
root. -/
private theorem cycleApp_first_root_mul (f : cycleNilpotentRep k n m ⟶ cycleNilpotentRep k n m)
    (x : AdjoinRoot ((X : k[X]) ^ (m + 1))) :
    cycleApp f Quiver.Cycle.first (AdjoinRoot.root ((X : k[X]) ^ (m + 1)) * x) =
      AdjoinRoot.root ((X : k[X]) ^ (m + 1)) * cycleApp f Quiver.Cycle.first x := by
  have hx := cycleApp_weight_mul f Quiver.Cycle.last x
  rw [cycleNilpotentWeight_last, cycleApp_eq_first f (Quiver.Cycle.last.succ),
    cycleApp_eq_first f Quiver.Cycle.last] at hx
  exact hx

/-- **Every endomorphism is multiplication by its value at `1`.** -/
private theorem cycleApp_eq_mulRight (f : cycleNilpotentRep k n m ⟶ cycleNilpotentRep k n m)
    (i : Quiver.Cycle n) :
    cycleApp f i = LinearMap.mulRight k (cycleApp f Quiver.Cycle.first 1) :=
  (cycleApp_eq_first f i).trans
    (AdjoinRoot.eq_mulRight_of_root_mul (monic_X_pow (R := k) (m + 1))
      (cycleApp_first_root_mul f))

/-- Every component of an endomorphism is multiplication by the same element, its value at `1` at
the first vertex. -/
private theorem cycleApp_apply (f : cycleNilpotentRep k n m ⟶ cycleNilpotentRep k n m)
    (i : Quiver.Cycle n) (x : AdjoinRoot ((X : k[X]) ^ (m + 1))) :
    cycleApp f i x = x * cycleApp f Quiver.Cycle.first 1 := by
  rw [cycleApp_eq_mulRight f i, LinearMap.mulRight_apply]

/-- `TauCeti.cycleNilpotentRep k n m` is finite-dimensional: every vertex space is
`k[X]/(Xᵐ⁺¹)`. -/
theorem isFinDim_cycleNilpotentRep :
    IsFinDim k (Quiver.Cycle n) (cycleNilpotentRep k n m) :=
  isFinDim_iff.mpr fun _ ↦ (monic_X_pow (R := k) (m + 1)).finite_adjoinRoot

/-- The dimension vector of `TauCeti.cycleNilpotentRep k n m` is the constant `m + 1`. -/
theorem dimVector_cycleNilpotentRep (i : Quiver.Cycle n) :
    dimVector (cycleNilpotentRep k n m) i = m + 1 := by
  rw [dimVector_apply, cycleNilpotentRep_obj]
  exact finrank_quotient_span_eq_natDegree.trans (natDegree_X_pow (m + 1))

/-- `TauCeti.cycleNilpotentRep k n m` is nonzero: its vertex spaces are the nontrivial ring
`k[X]/(Xᵐ⁺¹)`. -/
theorem not_isZero_cycleNilpotentRep : ¬ IsZero (cycleNilpotentRep k n m) := by
  intro h
  have : Subsingleton (AdjoinRoot ((X : k[X]) ^ (m + 1))) :=
    ModuleCat.subsingleton_of_isZero
      (h.obj ((Quiver.Cycle.first : Quiver.Cycle n) : Paths (Quiver.Cycle n)))
  exact false_of_nontrivial_of_subsingleton (AdjoinRoot ((X : k[X]) ^ (m + 1)))

/-- **`TauCeti.cycleNilpotentRep k n m` is indecomposable.** Its endomorphisms are constant along
the cycle and commute with multiplication by the root, hence are multiplication by their value at
`1`, so that value records them faithfully in the local ring `k[X]/(Xᵐ⁺¹)`, sending `0` to `0`, the
identity to `1` and squares to squares. -/
theorem indecomposable_cycleNilpotentRep : Indecomposable (cycleNilpotentRep k n m) := by
  refine indecomposable_of_injective_of_isLocalRing not_isZero_cycleNilpotentRep
    (fun f ↦ cycleApp f Quiver.Cycle.first 1) (fun f g h ↦ ?_) ?_ ?_ fun e ↦ ?_
  · refine cycleNilpotentRep_hom_ext fun i ↦ LinearMap.ext fun x ↦ ?_
    rw [cycleApp_apply f i x, cycleApp_apply g i x]
    exact congrArg (x * ·) h
  · rw [cycleApp_zero, LinearMap.zero_apply]
  · rw [cycleApp_id, LinearMap.id_apply]
  · rw [cycleApp_comp, LinearMap.comp_apply,
      cycleApp_apply e Quiver.Cycle.first (cycleApp e Quiver.Cycle.first 1)]

/-- **Nilpotent cycle representations of different sizes are non-isomorphic**: their dimension
vectors differ. -/
theorem eq_of_nonempty_cycleNilpotentRep_iso {m m' : ℕ}
    (h : Nonempty (cycleNilpotentRep k n m ≅ cycleNilpotentRep k n m')) : m = m' := by
  obtain ⟨e⟩ := h
  have hd := congrFun (dimVector_eq_of_iso e) Quiver.Cycle.first
  rw [dimVector_cycleNilpotentRep, dimVector_cycleNilpotentRep] at hd
  omega

/-- Two nilpotent cycle representations are isomorphic exactly when their sizes agree. -/
@[simp]
theorem nonempty_cycleNilpotentRep_iso_iff {m m' : ℕ} :
    Nonempty (cycleNilpotentRep k n m ≅ cycleNilpotentRep k n m') ↔ m = m' :=
  ⟨eq_of_nonempty_cycleNilpotentRep_iso, by rintro rfl; exact ⟨Iso.refl _⟩⟩

/-- **The cycle quiver has infinite representation type over every field.** The nilpotent
representations `TauCeti.cycleNilpotentRep k n m` are finite-dimensional, indecomposable and
pairwise non-isomorphic, so `ℕ` indexes an infinite family of them. -/
theorem not_isFiniteRepType_cycle (k : Type u) [Field k] (n : ℕ) :
    ¬ IsFiniteRepType.{u, 0, 0, u} k (Quiver.Cycle n) :=
  not_isFiniteRepType_of_infinite (M := cycleNilpotentRep k n)
    (fun _ ↦ isFinDim_cycleNilpotentRep) (fun _ ↦ indecomposable_cycleNilpotentRep)
    fun _ _ hne h ↦ hne (eq_of_nonempty_cycleNilpotentRep_iso h)

end TauCeti

end
