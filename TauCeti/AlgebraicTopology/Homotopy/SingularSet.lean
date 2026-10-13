/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex
public import TauCeti.AlgebraicTopology.SimplicialSet.KanComplex.HomotopyGroup
public import TauCeti.AlgebraicTopology.SimplicialSet.TopAdj
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map
public import TauCeti.Topology.Homotopy.HomotopyGroup.Simplex

/-!
# Simplicial and cubical homotopy groups of a space

For a topological space `X` with a point `x`, the singular simplicial set `TopCat.toSSet.obj X`
is a Kan complex (`TopCat.kanComplex_toSSet_obj`), so it has combinatorial homotopy groups
`SSet.KanComplex.π (n + 1) (TopCat.toSSet.obj X) x`, built from pointed simplices
`Δ[n + 1] ⟶ TopCat.toSSet.obj X` up to homotopy relative to the boundary. Mathlib's homotopy
groups `HomotopyGroup (Fin (n + 1)) X x` are built instead from generalized loops `Iⁿ⁺¹ → X` up
to homotopy relative to the boundary of the cube. This file identifies the two, naturally in
based maps (`TopCat.toSSetPiEquivHomotopyGroup`, `TopCat.toSSetPiEquivHomotopyGroup_map`).

* A pointed `(n + 1)`-simplex of `TopCat.toSSet.obj X` at `x` is a continuous map `Δⁿ⁺¹ → X`
  sending every facet to `x` (`TopCat.ptSimplexEquiv`), and precomposition with the quotient
  map `Convexity.StdSimplex.ofCube (n + 1) : Iⁿ⁺¹ → Δⁿ⁺¹` turns these maps bijectively into
  generalized loops (`GenLoop.simplexEquiv`).
* In a Kan complex, two pointed simplices `p` and `q` are homotopic exactly when they are related
  by `SSet.PtSimplex.RelStruct₀`: they are the faces `0` and `1` of an `(n + 2)`-simplex whose
  other faces are constant. For the singular simplicial set this is a continuous map
  `Δⁿ⁺² → X` with these faces (`TopCat.nonempty_relStruct₀_iff`), which is exactly the condition
  for the corresponding generalized loops to be homotopic relative to the boundary
  (`GenLoop.homotopic_simplexEquiv_iff`).

The bijection sends the identity element to the identity element
(`TopCat.toSSetPiEquivHomotopyGroup_one`), and it reverses products
(`TopCat.toSSetPiEquivHomotopyGroup_mul_reverse`). A product `π.mk p * π.mk q` is witnessed by a
map `Δⁿ⁺² → X` whose facets `n + 2`, `n + 1` and `n` are `p`, the product and `q`, so the product
runs `p` before `q` in the last direction of the cube
(`GenLoop.homotopic_simplexEquiv_transAt_last`), whereas Mathlib's product `⟦f⟧ * ⟦g⟧` runs `g`
before `f`. So in every positive degree the bijection is a group isomorphism onto the opposite of
Mathlib's homotopy group (`TopCat.toSSetPiMulEquivHomotopyGroupMulOpposite`). In degrees at least
two Mathlib's homotopy groups are commutative, so the bijection is a group isomorphism
(`TopCat.toSSetPiMulEquivHomotopyGroup`).

## Main declarations

* `TopCat.ptSimplexEquiv`: pointed simplices of the singular simplicial set as maps out of a
  simplex sending every facet to the base point.
* `TopCat.nonempty_relStruct₀_iff`: the relation `SSet.PtSimplex.RelStruct₀` in the singular
  simplicial set, in terms of maps out of a simplex.
* `TopCat.toSSetPiEquivHomotopyGroup`: the bijection
  `SSet.KanComplex.π (n + 1) (TopCat.toSSet.obj X) x ≃ HomotopyGroup (Fin (n + 1)) X x`, with
  `TopCat.toSSetPiEquivHomotopyGroup_mk` its value on a pointed simplex and
  `TopCat.toSSetPiEquivHomotopyGroup_map` its naturality.
* `TopCat.toSSetPiEquivHomotopyGroup_mul_reverse`, `TopCat.toSSetPiEquivHomotopyGroup_inv`: the
  bijection reverses products and preserves inverses.
* `TopCat.toSSetPiMulEquivHomotopyGroupMulOpposite`: the group isomorphism onto the opposite of
  Mathlib's homotopy group, in every positive degree.
* `TopCat.toSSetPiMulEquivHomotopyGroup`: the group isomorphism in degrees at least two.

## References

* J. P. May, *Simplicial Objects in Algebraic Topology*, University of Chicago Press, 1967,
  §16, for the comparison of the homotopy groups of the singular complex of a space with those of
  the space.
-/

public noncomputable section

universe u

open CategoryTheory Simplicial Convexity SSet TauCeti.TopCat
open scoped Topology.Homotopy

namespace TopCat

variable (X : TopCat.{u}) (x : X) (n : ℕ)

/-- The pointed `(n + 1)`-simplices of the singular simplicial set of `X` at `x` are the maps
`Δⁿ⁺¹ → X` sending every facet to `x`. -/
def ptSimplexEquiv : (toSSet.obj X).PtSimplex (n + 1) (toSSetObj₀Equiv.symm x) ≃
    {φ : C(StdSimplex ℝ (Fin (n + 2)), X) //
      ∀ (i : Fin (n + 2)) (z : StdSimplex ℝ (Fin (n + 1))), φ (z.map i.succAbove) = x} where
  toFun p := ⟨X.toSSetObjEquiv _ (yonedaEquiv p.map), fun i z => by
    have := congrArg (fun f => X.toSSetObjEquiv _ (yonedaEquiv f) z) (p.δ_map i)
    simpa only [toSSetObjEquiv_yonedaEquiv_δ_comp_apply,
      toSSetObjEquiv_yonedaEquiv_const_apply] using this⟩
  invFun φ :=
    { map := yonedaEquiv.symm ((X.toSSetObjEquiv _).symm φ.1)
      comm := by
        ext i : 1
        simp only [boundary.ι_ι_assoc, comp_const, const_comp]
        refine hom_ext_stdSimplex fun z => ?_
        rw [toSSetObjEquiv_yonedaEquiv_δ_comp_apply, Equiv.apply_symm_apply,
          Equiv.apply_symm_apply]
        exact φ.2 i z }
  left_inv p := by ext : 1; simp
  right_inv φ := by ext : 1; simp

variable {X x n}

@[simp]
lemma ptSimplexEquiv_symm_apply_map
    (φ : {φ : C(StdSimplex ℝ (Fin (n + 2)), X) //
      ∀ (i : Fin (n + 2)) (z : StdSimplex ℝ (Fin (n + 1))), φ (z.map i.succAbove) = x}) :
    ((ptSimplexEquiv X x n).symm φ).map = yonedaEquiv.symm ((X.toSSetObjEquiv _).symm φ.1) :=
  (rfl)

@[simp]
lemma coe_ptSimplexEquiv_apply (p : (toSSet.obj X).PtSimplex (n + 1) (toSSetObj₀Equiv.symm x)) :
    (ptSimplexEquiv X x n p : C(StdSimplex ℝ (Fin (n + 2)), X)) =
      X.toSSetObjEquiv _ (yonedaEquiv p.map) :=
  (rfl)

/-- Two pointed simplices `p` and `q` of the singular simplicial set are related by
`SSet.PtSimplex.RelStruct₀` exactly when they are the facets `0` and `1` of a map `Δⁿ⁺² → X`
sending its other facets to `x`. -/
theorem nonempty_relStruct₀_iff
    {p q : (toSSet.obj X).PtSimplex (n + 1) (toSSetObj₀Equiv.symm x)} :
    Nonempty (p.RelStruct₀ q) ↔
      ∃ τ : C(StdSimplex ℝ (Fin (n + 3)), X),
        (∀ z : StdSimplex ℝ (Fin (n + 2)),
          τ (z.map (0 : Fin (n + 3)).succAbove) = (ptSimplexEquiv X x n p).1 z) ∧
        (∀ z : StdSimplex ℝ (Fin (n + 2)),
          τ (z.map (1 : Fin (n + 3)).succAbove) = (ptSimplexEquiv X x n q).1 z) ∧
        ∀ j : Fin (n + 3), 1 < j → ∀ z : StdSimplex ℝ (Fin (n + 2)),
          τ (z.map j.succAbove) = x := by
  constructor
  · rintro ⟨h⟩
    refine ⟨X.toSSetObjEquiv _ (yonedaEquiv h.map), fun z => ?_, fun z => ?_, fun j hj z => ?_⟩
    · have := congrArg (fun f => X.toSSetObjEquiv _ (yonedaEquiv f) z) h.δ_castSucc_map
      simp only [toSSetObjEquiv_yonedaEquiv_δ_comp_apply, Fin.castSucc_zero] at this
      exact this
    · have := congrArg (fun f => X.toSSetObjEquiv _ (yonedaEquiv f) z) h.δ_succ_map
      simp only [toSSetObjEquiv_yonedaEquiv_δ_comp_apply, Fin.succ_zero_eq_one] at this
      exact this
    · have := congrArg (fun f => X.toSSetObjEquiv _ (yonedaEquiv f) z)
        (h.δ_map_of_gt j (by simpa using hj))
      simpa only [toSSetObjEquiv_yonedaEquiv_δ_comp_apply,
        toSSetObjEquiv_yonedaEquiv_const_apply] using this
  · rintro ⟨τ, h0, h1, hj⟩
    exact ⟨{ map := yonedaEquiv.symm ((X.toSSetObjEquiv _).symm τ)
             δ_castSucc_map := hom_ext_stdSimplex fun z => by simpa using h0 z
             δ_succ_map := hom_ext_stdSimplex fun z => by simpa using h1 z
             δ_map_of_lt := fun j hj => absurd hj (Fin.not_lt_zero _)
             δ_map_of_gt := fun j hj' => hom_ext_stdSimplex fun z => by
               simpa using hj j (by simpa using hj') z }⟩

/-- Two pointed simplices of the singular simplicial set are related by
`SSet.PtSimplex.RelStruct₀` exactly when the corresponding generalized loops are homotopic. -/
private lemma nonempty_relStruct₀_iff_homotopic
    {p q : (toSSet.obj X).PtSimplex (n + 1) (toSSetObj₀Equiv.symm x)} :
    Nonempty (p.RelStruct₀ q) ↔ GenLoop.Homotopic
      (GenLoop.simplexEquiv X x (n + 1) (ptSimplexEquiv X x n p))
      (GenLoop.simplexEquiv X x (n + 1) (ptSimplexEquiv X x n q)) :=
  nonempty_relStruct₀_iff.trans GenLoop.homotopic_simplexEquiv_iff.symm

variable (X x n) in
/-- The homotopy groups of the singular simplicial set of `X`, a Kan complex, are the homotopy
groups of `X`: a pointed simplex `Δⁿ⁺¹ → X` is sent to the generalized loop obtained by
precomposition with `Convexity.StdSimplex.ofCube (n + 1) : Iⁿ⁺¹ → Δⁿ⁺¹`. -/
def toSSetPiEquivHomotopyGroup :
    KanComplex.π (n + 1) (toSSet.obj X) (toSSetObj₀Equiv.symm x) ≃
      HomotopyGroup (Fin (n + 1)) X x := by
  refine Equiv.ofBijective (KanComplex.π.lift (α := HomotopyGroup (Fin (n + 1)) X x)
    (fun p => ⟦GenLoop.simplexEquiv X x (n + 1) (ptSimplexEquiv X x n p)⟧)
    fun p q h => Quotient.sound
      (nonempty_relStruct₀_iff_homotopic.1 ⟨PtSimplex.Homotopy.relStruct₀ h⟩)) ⟨?_, ?_⟩
  · intro a b hab
    induction a with | mk p
    induction b with | mk q
    have h : (⟦GenLoop.simplexEquiv X x (n + 1) (ptSimplexEquiv X x n p)⟧ :
        HomotopyGroup (Fin (n + 1)) X x) =
          ⟦GenLoop.simplexEquiv X x (n + 1) (ptSimplexEquiv X x n q)⟧ :=
      (KanComplex.π.lift_mk _ _ p).symm.trans (hab.trans (KanComplex.π.lift_mk _ _ q))
    exact KanComplex.π.mk_eq_mk_iff.2 (nonempty_relStruct₀_iff_homotopic.2 (Quotient.exact h))
  · refine Quotient.ind fun g => ⟨KanComplex.π.mk ((ptSimplexEquiv X x n).symm
      ((GenLoop.simplexEquiv X x (n + 1)).symm g)), ?_⟩
    exact (KanComplex.π.lift_mk _ _ _).trans (congrArg _ (by simp))

@[simp]
lemma toSSetPiEquivHomotopyGroup_mk
    (p : (toSSet.obj X).PtSimplex (n + 1) (toSSetObj₀Equiv.symm x)) :
    toSSetPiEquivHomotopyGroup X x n (KanComplex.π.mk p) =
      ⟦GenLoop.simplexEquiv X x (n + 1) (ptSimplexEquiv X x n p)⟧ :=
  KanComplex.π.lift_mk _ _ p

@[simp]
lemma toSSetPiEquivHomotopyGroup_symm_mk (g : Ω^ (Fin (n + 1)) X x) :
    (toSSetPiEquivHomotopyGroup X x n).symm ⟦g⟧ =
      KanComplex.π.mk
        ((ptSimplexEquiv X x n).symm ((GenLoop.simplexEquiv X x (n + 1)).symm g)) := by
  refine (Equiv.symm_apply_eq _).2 (Eq.trans ?_ (toSSetPiEquivHomotopyGroup_mk _).symm)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]

/-- The comparison of homotopy groups sends the class of the constant pointed simplex to the
class of the constant generalized loop. -/
@[simp]
lemma toSSetPiEquivHomotopyGroup_one : toSSetPiEquivHomotopyGroup X x n 1 = 1 := by
  rw [KanComplex.π.one_def, toSSetPiEquivHomotopyGroup_mk, ← HomotopyGroup.mk_const_eq_one]
  congr 1
  ext t
  simp

/-- The comparison of homotopy groups is natural in based maps. -/
theorem toSSetPiEquivHomotopyGroup_map {Y : TopCat.{u}} (f : X ⟶ Y)
    (a : KanComplex.π (n + 1) (toSSet.obj X) (toSSetObj₀Equiv.symm x)) :
    toSSetPiEquivHomotopyGroup Y (f x) n
        (KanComplex.π.map (toSSet.map f) (toSSet_map_app_toSSetObj₀Equiv_symm f x) a) =
      HomotopyGroup.map f.hom rfl (toSSetPiEquivHomotopyGroup X x n a) := by
  induction a with
  | mk p =>
    rw [KanComplex.π.map_mk, toSSetPiEquivHomotopyGroup_mk, toSSetPiEquivHomotopyGroup_mk,
      HomotopyGroup.map_mk]
    exact congrArg _ (GenLoop.ext _ _ fun t => by simp [yonedaEquiv_comp])

/-- The comparison of homotopy groups reverses products. The product `π.mk p * π.mk q` is the
class of the facet `n + 1` of an `(n + 2)`-simplex whose facets `n + 2` and `n` are `p` and `q`
(`SSet.KanComplex.π.mul_mk_eq_iff`), which runs `p` before `q` in the last direction of the
cube, whereas Mathlib's product `⟦f⟧ * ⟦g⟧` runs `g` before `f` (`HomotopyGroup.mul_spec`). -/
@[simp]
theorem toSSetPiEquivHomotopyGroup_mul_reverse
    (a b : KanComplex.π (n + 1) (toSSet.obj X) (toSSetObj₀Equiv.symm x)) :
    toSSetPiEquivHomotopyGroup X x n (a * b) =
      toSSetPiEquivHomotopyGroup X x n b * toSSetPiEquivHomotopyGroup X x n a := by
  induction a with | mk p
  induction b with | mk q
  obtain ⟨pq, ⟨h⟩⟩ := PtSimplex.MulStruct.nonempty p q (Fin.last n)
  rw [h.mul_eq, toSSetPiEquivHomotopyGroup_mk, toSSetPiEquivHomotopyGroup_mk,
    toSSetPiEquivHomotopyGroup_mk]
  -- The facets of the simplex of `h`, read as continuous maps out of the topological simplex.
  have hface {j : Fin (n + 3)} {r : (toSSet.obj X).PtSimplex (n + 1) (toSSetObj₀Equiv.symm x)}
      (hj : stdSimplex.δ j ≫ h.map = r.map) (z : StdSimplex ℝ (Fin (n + 2))) :
      X.toSSetObjEquiv _ (yonedaEquiv h.map) (z.map j.succAbove) =
        (ptSimplexEquiv X x n r).1 z := by
    have := congrArg (fun f => X.toSSetObjEquiv _ (yonedaEquiv f) z) hj
    simpa only [toSSetObjEquiv_yonedaEquiv_δ_comp_apply, coe_ptSimplexEquiv_apply] using this
  refine (Quotient.sound (GenLoop.homotopic_simplexEquiv_transAt_last
    (X.toSSetObjEquiv _ (yonedaEquiv h.map))
    (fun j hj z => ?_) (hface h.δ_castSucc_castSucc_map) (hface h.δ_succ_castSucc_map)
    (hface h.δ_succ_succ_map))).trans (HomotopyGroup.mul_spec (i := Fin.last n)).symm
  have := congrArg (fun f => X.toSSetObjEquiv _ (yonedaEquiv f) z) (h.δ_map_of_lt j hj)
  simpa only [toSSetObjEquiv_yonedaEquiv_δ_comp_apply,
    toSSetObjEquiv_yonedaEquiv_const_apply] using this

/-- The comparison of homotopy groups commutes with inverses. -/
@[simp]
lemma toSSetPiEquivHomotopyGroup_inv
    (a : KanComplex.π (n + 1) (toSSet.obj X) (toSSetObj₀Equiv.symm x)) :
    toSSetPiEquivHomotopyGroup X x n a⁻¹ = (toSSetPiEquivHomotopyGroup X x n a)⁻¹ := by
  -- The unit of the group `π (n + 1)` is not exposed as the `1` of
  -- `toSSetPiEquivHomotopyGroup_one`. Instead, `a * a⁻¹` is idempotent, so its image is
  -- idempotent, hence the identity.
  have hidem : a * a⁻¹ * (a * a⁻¹) = a * a⁻¹ := by rw [mul_inv_cancel, mul_one]
  have he := congrArg (toSSetPiEquivHomotopyGroup X x n) hidem
  rw [toSSetPiEquivHomotopyGroup_mul_reverse, mul_eq_left] at he
  exact eq_inv_of_mul_eq_one_left (by rw [← toSSetPiEquivHomotopyGroup_mul_reverse, he])

variable (X x n) in
/-- In every positive degree, the comparison of the homotopy groups of the singular simplicial set
of `X` with those of `X` is a group isomorphism onto the opposite of Mathlib's homotopy group,
since it reverses products (`TopCat.toSSetPiEquivHomotopyGroup_mul_reverse`). -/
def toSSetPiMulEquivHomotopyGroupMulOpposite :
    KanComplex.π (n + 1) (toSSet.obj X) (toSSetObj₀Equiv.symm x) ≃*
      (HomotopyGroup (Fin (n + 1)) X x)ᵐᵒᵖ where
  toEquiv := (toSSetPiEquivHomotopyGroup X x n).trans MulOpposite.opEquiv
  map_mul' a b := congrArg MulOpposite.op (toSSetPiEquivHomotopyGroup_mul_reverse a b)

@[simp]
lemma toSSetPiMulEquivHomotopyGroupMulOpposite_apply
    (a : KanComplex.π (n + 1) (toSSet.obj X) (toSSetObj₀Equiv.symm x)) :
    toSSetPiMulEquivHomotopyGroupMulOpposite X x n a =
      MulOpposite.op (toSSetPiEquivHomotopyGroup X x n a) :=
  (rfl)

variable (X x n) in
/-- In degrees at least two, where Mathlib's homotopy groups are commutative, the comparison of the
homotopy groups of the singular simplicial set of `X` with those of `X` is a group
isomorphism. -/
def toSSetPiMulEquivHomotopyGroup :
    KanComplex.π (n + 2) (toSSet.obj X) (toSSetObj₀Equiv.symm x) ≃*
      HomotopyGroup (Fin (n + 2)) X x :=
  (toSSetPiMulEquivHomotopyGroupMulOpposite X x (n + 1)).trans MulOpposite.opMulEquiv.symm

@[simp]
lemma coe_toSSetPiMulEquivHomotopyGroup :
    ⇑(toSSetPiMulEquivHomotopyGroup X x n) = toSSetPiEquivHomotopyGroup X x (n + 1) :=
  (rfl)

@[simp]
lemma toSSetPiMulEquivHomotopyGroup_toEquiv :
    (toSSetPiMulEquivHomotopyGroup X x n : _ ≃ _) = toSSetPiEquivHomotopyGroup X x (n + 1) :=
  (rfl)

end TopCat
