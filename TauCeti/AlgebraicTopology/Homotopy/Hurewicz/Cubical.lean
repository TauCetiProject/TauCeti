/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.ModuleCat.Basic
public import TauCeti.AlgebraicTopology.Singular.Cubical.ChainComplex
public import TauCeti.AlgebraicTopology.Singular.Cubical.Prism
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map
public import TauCeti.Topology.Homotopy.HomotopyGroup.TransAt

/-!
# The cubical Hurewicz homomorphism

A generalized loop `p : Ω^ (Fin (n + 1)) X x` is a singular `(n + 1)`-cube of `X` sending the
boundary of the cube to `x`, so all of its faces are the constant cube at `x`
(`GenLoop.face_eq_const`) and it is a cycle of the normalized cubical chains
(`GenLoop.boundary_ofCube_eq_zero`). Its class in normalized cubical homology is the
**cubical Hurewicz class** `GenLoop.cubicalHurewicz R p`, for any coefficient ring `R`.

This file shows that the cubical Hurewicz class only depends on the homotopy class of `p` and
that it turns the product of `π_{n+1}(X, x)` into the sum of homology classes, so that it defines
a homomorphism

`HomotopyGroup.cubicalHurewiczHom R n : π_{n+1}(X, x) →+ H^□ₙ₊₁(X; R)`,

natural in based maps (`HomotopyGroup.cubicalHurewicz_map`). Both facts are witnessed by explicit
cubes of one dimension more.

* A homotopy `H` relative to the boundary from `p` to `q` sweeps out an `(n + 2)`-cube
  (`TauCeti.SingularCube.prism`), with time as the first coordinate. Its two faces in the first
  coordinate are `p` and `q`, and all of its other faces are constant, so its boundary is `p - q`.
* Mathlib represents the product `[p] * [q]` by the concatenation `f = transAt 0 q p`, which runs
  `q` on the first half of the first coordinate and `p` on the second half. Precomposing `f` with
  the reparametrisation `(s, t, w) ↦ (s / 2 + t (1 - s / 2), w)` gives an `(n + 2)`-cube whose
  faces are `f` and `p` for `s = 0, 1`, `q` and the constant cube for `t = 0, 1`, and constant
  cubes in the remaining coordinates. Constant cubes of positive dimension are degenerate, so its
  boundary is `f - p - q` in the normalized chains.

In normalized cubical chains a generalized loop is itself a cycle, with no choice of
representative or of a generator of the homology of the cube. This makes the cubical Hurewicz map
the form of the Hurewicz map suited to chain-level arguments, such as Eilenberg's deformation of
the singular chains of an `(n - 1)`-connected space into combinations of generalized loops.

## Main definitions

* `GenLoop.cubicalHurewicz R p`: the class of a generalized loop in normalized cubical homology,
  characterized by `GenLoop.homologyπ_eq_cubicalHurewicz`.
* `HomotopyGroup.cubicalHurewicz R n`: the induced map on `π_{n+1}(X, x)`.
* `HomotopyGroup.cubicalHurewiczHom R n`: the same map, as a homomorphism from `π_{n+1}(X, x)`
  written additively.

## Main results

* `GenLoop.cubicalHurewicz_eq_of_homotopic`: homotopic generalized loops have the same class.
* `HomotopyGroup.cubicalHurewicz_mul`: the cubical Hurewicz map is additive.
* `GenLoop.cubicalHurewicz_map`, `HomotopyGroup.cubicalHurewicz_map`: naturality in based maps.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II, for singular cubes
  and normalized cubical chains.
* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407–447, for the
  comparison of homotopy and homology through singular chains sending a skeleton to the base point.
-/

public section

noncomputable section

open CategoryTheory TauCeti
open scoped unitInterval Topology Topology.Homotopy

universe u

namespace GenLoop

section Cubes

variable {X : Type*} [TopologicalSpace X] {x : X} {n : ℕ}

/-- Every face of a generalized loop, read as a singular cube, is the constant cube at the base
point. -/
theorem face_eq_const (p : Ω^ (Fin (n + 1)) X x) (i : Fin (n + 1)) {t : I} (ht : t = 0 ∨ t = 1) :
    SingularCube.face i t (p : SingularCube X (n + 1)) = ContinuousMap.const _ x := by
  ext z
  rw [SingularCube.face_apply, ContinuousMap.const_apply]
  exact GenLoop.boundary p _ ⟨i, by rwa [Fin.insertNth_apply_same]⟩

variable (R : Type*) [Ring R]

/-- A generalized loop is a cycle of the normalized cubical chains. -/
@[simp]
theorem boundary_ofCube_eq_zero (p : Ω^ (Fin (n + 1)) X x) :
    NormalizedCubicalChain.boundary X R n
      (NormalizedCubicalChain.ofCube X R (p : SingularCube X (n + 1))) = 0 := by
  rw [NormalizedCubicalChain.boundary_ofCube]
  refine Finset.sum_eq_zero fun i _ ↦ ?_
  rw [face_eq_const p i (.inl rfl), face_eq_const p i (.inr rfl), sub_self, smul_zero]

/-! ### The cube swept out by a homotopy -/

/-- The faces outside the time coordinate of the cube swept out by a homotopy of generalized loops
relative to the boundary are constant. -/
private lemma face_succ_prism_eq_const {p q : Ω^ (Fin (n + 1)) X x}
    (H : p.1.HomotopyRel q.1 (Cube.boundary (Fin (n + 1)))) (j : Fin (n + 1)) {t : I}
    (ht : t = 0 ∨ t = 1) :
    SingularCube.face j.succ t (SingularCube.prism H.toHomotopy (ContinuousMap.id _)) =
      ContinuousMap.const _ x := by
  ext z
  rw [SingularCube.face_succ_prism, SingularCube.prism_apply, SingularCube.face_apply,
    ContinuousMap.id_apply, ContinuousMap.const_apply]
  have hb : Fin.insertNth (α := fun _ ↦ I) j t (Fin.tail z) ∈ Cube.boundary (Fin (n + 1)) :=
    ⟨j, by rwa [Fin.insertNth_apply_same]⟩
  exact (H.eq_fst _ hb).trans (GenLoop.boundary p _ hb)

/-- The boundary of the cube swept out by a homotopy relative to the boundary from `p` to `q` is
`p - q`. -/
private lemma boundary_ofCube_prism {p q : Ω^ (Fin (n + 1)) X x}
    (H : p.1.HomotopyRel q.1 (Cube.boundary (Fin (n + 1)))) :
    NormalizedCubicalChain.boundary X R (n + 1) (NormalizedCubicalChain.ofCube X R
      (SingularCube.prism H.toHomotopy (ContinuousMap.id _))) =
      NormalizedCubicalChain.ofCube X R (p : SingularCube X (n + 1)) -
        NormalizedCubicalChain.ofCube X R (q : SingularCube X (n + 1)) := by
  rw [NormalizedCubicalChain.boundary_ofCube, Fin.sum_univ_succ, SingularCube.face_zero_prism,
    SingularCube.face_one_prism, Finset.sum_eq_zero fun j _ ↦ by
      rw [face_succ_prism_eq_const H j (.inl rfl), face_succ_prism_eq_const H j (.inr rfl),
        sub_self, smul_zero]]
  simp

/-! ### The cube relating a concatenation to its two halves -/

/-- The reparametrisation `(s, t) ↦ s / 2 + t (1 - s / 2)` of the unit interval: it is `t` for
`s = 0`, `(1 + t) / 2` for `s = 1`, `s / 2` for `t = 0` and `1` for `t = 1`. -/
private def addParam (s t : I) : I :=
  ⟨s / 2 + t * (1 - s / 2), by
    constructor <;> nlinarith [s.2.1, s.2.2, t.2.1, t.2.2, mul_nonneg t.2.1 s.2.1]⟩

private lemma continuous_addParam : Continuous fun z : I × I ↦ addParam z.1 z.2 := by
  unfold addParam
  fun_prop

@[simp] private lemma coe_addParam (s t : I) : (addParam s t : ℝ) = s / 2 + t * (1 - s / 2) :=
  (rfl)

@[simp] private lemma addParam_zero_left (t : I) : addParam 0 t = t := by
  ext; simp

@[simp] private lemma addParam_one_right (s : I) : addParam s 1 = 1 := by
  ext; simp

/-- The point of `Iⁿ⁺¹` at which the cube `addCube` evaluates the concatenation. -/
private def addPoint (z : Fin (n + 2) → I) : Fin (n + 1) → I :=
  Fin.cons (addParam (z 0) (z 1)) (Fin.tail (Fin.tail z))

private lemma continuous_addPoint : Continuous (addPoint (n := n)) := by
  have h : Continuous fun z : Fin (n + 2) → I ↦ addParam (z 0) (z 1) :=
    continuous_addParam.comp (by fun_prop : Continuous fun z : Fin (n + 2) → I ↦ (z 0, z 1))
  exact h.finCons (continuous_pi fun _ ↦ continuous_apply _)

private lemma addPoint_insertNth_zero (t : I) (w : Fin (n + 1) → I) :
    addPoint (Fin.insertNth 0 t w) = Fin.cons (addParam t (w 0)) (Fin.tail w) := by
  simp [addPoint, Fin.insertNth_zero']

private lemma addPoint_insertNth_one (t : I) (w : Fin (n + 1) → I) :
    addPoint (Fin.insertNth 1 t w) = Fin.cons (addParam (w 0) t) (Fin.tail w) := by
  rw [← Fin.cons_self_tail w, ← Fin.succ_zero_eq_one, Fin.insertNth_succ_cons]
  simp [addPoint, Fin.insertNth_zero']

private lemma addPoint_insertNth_succ_succ_succ (j : Fin n) (t : I) (w : Fin (n + 1) → I) :
    addPoint (Fin.insertNth j.succ.succ t w) j.succ = t := by
  simp [addPoint, Fin.tail]

/-- The `(n + 2)`-cube `(s, t, w) ↦ (transAt 0 q p) (s / 2 + t (1 - s / 2), w)`, whose boundary is
`transAt 0 q p - p - q` in the normalized chains. -/
private def addCube (p q : Ω^ (Fin (n + 1)) X x) : SingularCube X (n + 2) :=
  ⟨fun z ↦ transAt 0 q p (addPoint z), (transAt 0 q p).1.continuous.comp continuous_addPoint⟩

private lemma addCube_apply (p q : Ω^ (Fin (n + 1)) X x) (z : Fin (n + 2) → I) :
    addCube p q z = transAt 0 q p (addPoint z) :=
  (rfl)

/-- A generalized loop is `x` at every point whose first coordinate is `0` or `1`. -/
private lemma apply_cons_eq (p : Ω^ (Fin (n + 1)) X x) {t : I} (ht : t = 0 ∨ t = 1)
    (w : Fin n → I) : p (Fin.cons t w) = x :=
  GenLoop.boundary p _ ⟨0, by rwa [Fin.cons_zero]⟩

private lemma face_zero_zero_addCube (p q : Ω^ (Fin (n + 1)) X x) :
    SingularCube.face 0 0 (addCube p q) = transAt 0 q p := by
  ext z
  rw [SingularCube.face_apply, addCube_apply, addPoint_insertNth_zero, addParam_zero_left,
    Fin.cons_self_tail, coe_coe]

private lemma face_zero_one_addCube (p q : Ω^ (Fin (n + 1)) X x) :
    SingularCube.face 0 1 (addCube p q) = p := by
  ext z
  rw [SingularCube.face_apply, addCube_apply, addPoint_insertNth_zero, coe_coe]
  rcases eq_or_lt_of_le (z 0).2.1 with h | h
  · -- On the face `z₀ = 0`, both sides are the base point.
    have hz : z 0 = 0 := Subtype.ext h.symm
    rw [transAt_apply_of_le 0 q p (a := 1) (by simp [hz]) (by simp [hz]), Fin.update_cons_zero,
      apply_cons_eq q (.inr rfl), ← Fin.cons_self_tail z, hz, apply_cons_eq p (.inl rfl)]
  · rw [transAt_apply_of_lt 0 q p (a := z 0) (by simp; linarith) (by simp; ring),
      Fin.update_cons_zero, Fin.cons_self_tail]

private lemma face_one_zero_addCube (p q : Ω^ (Fin (n + 1)) X x) :
    SingularCube.face 1 0 (addCube p q) = q := by
  ext z
  rw [SingularCube.face_apply, addCube_apply, addPoint_insertNth_one, coe_coe,
    transAt_apply_of_le 0 q p (a := z 0) (by simp; linarith [(z 0).2.2]) (by simp; ring),
    Fin.update_cons_zero, Fin.cons_self_tail]

private lemma face_one_one_addCube (p q : Ω^ (Fin (n + 1)) X x) :
    SingularCube.face 1 1 (addCube p q) = ContinuousMap.const _ x := by
  ext z
  rw [SingularCube.face_apply, addCube_apply, addPoint_insertNth_one, addParam_one_right,
    ContinuousMap.const_apply]
  exact apply_cons_eq _ (.inr rfl) _

private lemma face_succ_succ_addCube (p q : Ω^ (Fin (n + 1)) X x) (j : Fin n) {t : I}
    (ht : t = 0 ∨ t = 1) :
    SingularCube.face j.succ.succ t (addCube p q) = ContinuousMap.const _ x := by
  ext z
  rw [SingularCube.face_apply, addCube_apply, ContinuousMap.const_apply]
  exact GenLoop.boundary _ _ ⟨j.succ, by rwa [addPoint_insertNth_succ_succ_succ]⟩

/-- The boundary of `addCube p q` is `transAt 0 q p - p - q` in the normalized chains. -/
private lemma boundary_ofCube_addCube (p q : Ω^ (Fin (n + 1)) X x) :
    NormalizedCubicalChain.boundary X R (n + 1) (NormalizedCubicalChain.ofCube X R
      (addCube p q)) =
      NormalizedCubicalChain.ofCube X R (transAt 0 q p : SingularCube X (n + 1)) -
        (NormalizedCubicalChain.ofCube X R (p : SingularCube X (n + 1)) +
          NormalizedCubicalChain.ofCube X R (q : SingularCube X (n + 1))) := by
  rw [NormalizedCubicalChain.boundary_ofCube, Fin.sum_univ_succ, Fin.sum_univ_succ,
    Finset.sum_eq_zero fun j _ ↦ by
      rw [face_succ_succ_addCube p q j (.inl rfl), face_succ_succ_addCube p q j (.inr rfl),
        sub_self, smul_zero]]
  simp only [Fin.succ_zero_eq_one, face_zero_zero_addCube, face_zero_one_addCube,
    face_one_zero_addCube, face_one_one_addCube, NormalizedCubicalChain.ofCube_eq_zero,
    SingularCube.isDegenerate_const]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_smul, sub_zero,
    add_zero]
  abel

end Cubes

section Class

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y} {n : ℕ}
  (R : Type u) [Ring R]

/-- A generalized loop as a cycle of the normalized cubical chains. -/
private def cubicalCycle (p : Ω^ (Fin (n + 1)) X x) :
    ((normalizedCubicalChainComplex R).obj (TopCat.of X)).cycles (n + 1) :=
  ((normalizedCubicalChainComplex R).obj (TopCat.of X)).moduleCatCyclesMk
    (NormalizedCubicalChain.ofCube X R (p : SingularCube X (n + 1))) n (by simp)
    (by rw [normalizedCubicalChainComplex_obj_d_apply]; exact boundary_ofCube_eq_zero R p)

private lemma iCycles_cubicalCycle (p : Ω^ (Fin (n + 1)) X x) :
    ((normalizedCubicalChainComplex R).obj (TopCat.of X)).iCycles (n + 1) (cubicalCycle R p) =
      NormalizedCubicalChain.ofCube X R (p : SingularCube X (n + 1)) :=
  HomologicalComplex.iCycles_moduleCatCyclesMk ..

/-- **The cubical Hurewicz class of a generalized loop** `p : Iⁿ⁺¹ → X`: the class of the cycle
`p` in the normalized cubical homology `H^□ₙ₊₁(X; R)`. It is characterized by
`GenLoop.homologyπ_eq_cubicalHurewicz`. -/
def cubicalHurewicz (p : Ω^ (Fin (n + 1)) X x) :
    ((normalizedCubicalChainComplex R).obj (TopCat.of X)).homology (n + 1) :=
  ((normalizedCubicalChainComplex R).obj (TopCat.of X)).homologyπ (n + 1) (cubicalCycle R p)

/-- The homology class of any cycle whose underlying chain is the cube `p` is the cubical
Hurewicz class of `p`. -/
theorem homologyπ_eq_cubicalHurewicz (p : Ω^ (Fin (n + 1)) X x)
    {z : ((normalizedCubicalChainComplex R).obj (TopCat.of X)).cycles (n + 1)}
    (hz : ((normalizedCubicalChainComplex R).obj (TopCat.of X)).iCycles (n + 1) z =
      NormalizedCubicalChain.ofCube X R (p : SingularCube X (n + 1))) :
    ((normalizedCubicalChainComplex R).obj (TopCat.of X)).homologyπ (n + 1) z =
      cubicalHurewicz R p := by
  rw [cubicalHurewicz]
  congr 1
  apply HomologicalComplex.moduleCat_iCycles_injective
  rw [hz, iCycles_cubicalCycle]

/-! ### Homotopy invariance and additivity -/

/-- Homotopic generalized loops have the same cubical Hurewicz class. -/
theorem cubicalHurewicz_eq_of_homotopic {p q : Ω^ (Fin (n + 1)) X x}
    (h : _root_.GenLoop.Homotopic p q) : cubicalHurewicz R p = cubicalHurewicz R q := by
  obtain ⟨H⟩ := h
  refine HomologicalComplex.moduleCat_homologyπ_eq_of_iCycles_sub_eq_d _
    (m := n + 2)
    (NormalizedCubicalChain.ofCube X R (SingularCube.prism H.toHomotopy (ContinuousMap.id _))) ?_
  rw [iCycles_cubicalCycle, iCycles_cubicalCycle, normalizedCubicalChainComplex_obj_d_apply,
    boundary_ofCube_prism]
  -- The two sides differ only by reading `X` as the carrier of `TopCat.of X`.
  rfl

/-- The cubical Hurewicz class of the concatenation `transAt 0 q p`, which represents
`[p] * [q]`, is the sum of the classes of `p` and `q`. -/
private lemma cubicalHurewicz_transAt (p q : Ω^ (Fin (n + 1)) X x) :
    cubicalHurewicz R (transAt 0 q p) = cubicalHurewicz R p + cubicalHurewicz R q := by
  rw [cubicalHurewicz, cubicalHurewicz, cubicalHurewicz, ← map_add]
  refine HomologicalComplex.moduleCat_homologyπ_eq_of_iCycles_sub_eq_d _
    (m := n + 2) (NormalizedCubicalChain.ofCube X R (addCube p q)) ?_
  rw [map_add, iCycles_cubicalCycle, iCycles_cubicalCycle, iCycles_cubicalCycle,
    normalizedCubicalChainComplex_obj_d_apply, boundary_ofCube_addCube]
  -- The two sides differ only by reading `X` as the carrier of `TopCat.of X`.
  rfl

/-! ### Naturality -/

/-- **Naturality of the cubical Hurewicz class**: for a based map `f : (X, x) → (Y, y)`, the
cubical Hurewicz class of `f ∘ p` is the image of that of `p` under `f_*`. -/
theorem cubicalHurewicz_map (f : C(X, Y)) (hf : f x = y) (p : Ω^ (Fin (n + 1)) X x) :
    cubicalHurewicz R (GenLoop.map f hf p) =
      HomologicalComplex.homologyMap ((normalizedCubicalChainComplex R).map (TopCat.ofHom f))
        (n + 1) (cubicalHurewicz R p) := by
  rw [cubicalHurewicz, cubicalHurewicz, ← ModuleCat.comp_apply,
    HomologicalComplex.homologyπ_naturality,
    ModuleCat.comp_apply]
  refine homologyπ_eq_cubicalHurewicz R _ ?_ |>.symm
  rw [← ModuleCat.comp_apply, HomologicalComplex.cyclesMap_i, ModuleCat.comp_apply,
    iCycles_cubicalCycle, normalizedCubicalChainComplex_map_f_apply,
    NormalizedCubicalChain.map_ofCube]
  rfl

end Class

end GenLoop

namespace HomotopyGroup

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y] {x : X} {y : Y}
  (R : Type u) [Ring R] (n : ℕ)

/-- **The cubical Hurewicz map** `π_{n+1}(X, x) → H^□ₙ₊₁(X; R)`, sending the class of a
generalized loop `p` to the class `GenLoop.cubicalHurewicz R p` of the cycle `p` in normalized
cubical homology. -/
def cubicalHurewicz :
    HomotopyGroup (Fin (n + 1)) X x →
      ((normalizedCubicalChainComplex R).obj (TopCat.of X)).homology (n + 1) :=
  Quotient.lift (GenLoop.cubicalHurewicz R) fun _ _ h ↦
    GenLoop.cubicalHurewicz_eq_of_homotopic R h

@[simp]
lemma cubicalHurewicz_mk (p : Ω^ (Fin (n + 1)) X x) :
    cubicalHurewicz R n (⟦p⟧ : HomotopyGroup (Fin (n + 1)) X x) = GenLoop.cubicalHurewicz R p :=
  (rfl)

/-- **The cubical Hurewicz map is additive**: it sends a product of homotopy classes to the sum
of their cubical Hurewicz classes. -/
@[simp]
theorem cubicalHurewicz_mul (a b : HomotopyGroup (Fin (n + 1)) X x) :
    cubicalHurewicz R n (a * b) = cubicalHurewicz R n a + cubicalHurewicz R n b := by
  refine Quotient.inductionOn₂ a b fun p q ↦ ?_
  -- `[p] * [q]` is the class of the concatenation `transAt 0 q p`.
  rw [cubicalHurewicz_mk, cubicalHurewicz_mk, ← GenLoop.cubicalHurewicz_transAt,
    ← cubicalHurewicz_mk, ← HomotopyGroup.mul_spec]

/-- The cubical Hurewicz map sends the identity class to zero. -/
@[simp]
theorem cubicalHurewicz_one : cubicalHurewicz R n (1 : HomotopyGroup (Fin (n + 1)) X x) = 0 :=
  left_eq_add.1 (by rw [← cubicalHurewicz_mul, one_mul])

/-- The cubical Hurewicz map sends the inverse of a class to the negative of its class. -/
@[simp]
theorem cubicalHurewicz_inv (a : HomotopyGroup (Fin (n + 1)) X x) :
    cubicalHurewicz R n a⁻¹ = -cubicalHurewicz R n a :=
  eq_neg_of_add_eq_zero_left (by rw [← cubicalHurewicz_mul, inv_mul_cancel, cubicalHurewicz_one])

/-- **Naturality of the cubical Hurewicz map**: for a based map `f : (X, x) → (Y, y)`, the cubical
Hurewicz class of `f_* a` is the image of the class of `a` under `f_*`. -/
theorem cubicalHurewicz_map (f : C(X, Y)) (hf : f x = y) (a : HomotopyGroup (Fin (n + 1)) X x) :
    cubicalHurewicz R n (HomotopyGroup.map f hf a) =
      HomologicalComplex.homologyMap ((normalizedCubicalChainComplex R).map (TopCat.ofHom f))
        (n + 1) (cubicalHurewicz R n a) :=
  Quotient.inductionOn a (GenLoop.cubicalHurewicz_map R f hf)

/-- **The cubical Hurewicz homomorphism** `π_{n+1}(X, x) → H^□ₙ₊₁(X; R)`, from the homotopy group
written additively to normalized cubical homology. -/
def cubicalHurewiczHom :
    Additive (HomotopyGroup (Fin (n + 1)) X x) →+
      ((normalizedCubicalChainComplex R).obj (TopCat.of X)).homology (n + 1) where
  toFun a := cubicalHurewicz R n a.toMul
  map_zero' := cubicalHurewicz_one R n
  map_add' a b := cubicalHurewicz_mul R n a.toMul b.toMul

@[simp]
lemma cubicalHurewiczHom_apply (a : Additive (HomotopyGroup (Fin (n + 1)) X x)) :
    cubicalHurewiczHom R n a = cubicalHurewicz R n a.toMul :=
  (rfl)

end HomotopyGroup
