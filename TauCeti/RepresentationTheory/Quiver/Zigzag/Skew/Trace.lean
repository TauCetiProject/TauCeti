/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.PerfectPairing.Basic
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Trace
public import TauCeti.RepresentationTheory.Quiver.Zigzag.Skew.Multiplication

/-!
# The Frobenius trace of a skew-zigzag algebra

The skew-zigzag relation quotient of a finite simple graph without isolated vertices is a
Frobenius algebra. After choosing one incident edge `t i` at every vertex, this file defines the
trace to be one on the corresponding volume classes and zero on vertex idempotents and arrows.
The pairing `(x, y) ↦ tr (x * y)` is associative and perfect.

Unlike the ordinary zigzag trace pairing, the skew pairing need not be symmetric. If `d : G.Dart`,
then the product of the arrow of `d` with the arrow of `d.symm` is the backtrack at `d.snd` along
`d.symm`. Relative to the chosen volume there, its trace is the unit

```text
c.ratio d.symm.adj (t d.snd).2.
```

These units are the nonzero entries of the Gram matrix. Thus the same basis involution as in the
ordinary case still locates the unique nonzero entry in every row, while the skew parameter gives
its value. This proves perfectness over an arbitrary commutative ring without inverting any scalar
outside the units already carried by the parameter. It also gives an exact criterion for the
chosen trace to be symmetric: the weights of a dart and its reverse must agree.

## Main definitions

* `TauCeti.skewZigzagPairingWeight`: the unit occurring in a row of the Gram matrix.
* `TauCeti.skewZigzagTrace`: the normalized trace attached to chosen incident edges.
* `TauCeti.skewZigzagTracePairing`: the associative pairing `(x, y) ↦ tr (x * y)`.

## Main results

* `TauCeti.skewZigzagTracePairing_skewZigzagBasisFun`: the weighted permutation Gram matrix.
* `TauCeti.skewZigzagTracePairing_isPerfPair`: the pairing is perfect.
* `TauCeti.skewZigzagTrace_mul_comm_iff`: the trace is symmetric exactly when opposite darts have
  equal pairing weights.

## References

This implements the Layer 1 instruction to normalize the skew Frobenius trace from the chosen
parameter and the Layer 2 instruction to extend the trace calculation to skew parameters in
`TauCetiRoadmap/ZigzagPreprojective/README.md`.

See C. Couture, *Skew-Zigzag Algebras*, Section 3,
https://arxiv.org/abs/1509.08405, and S. Huerfano and M. Khovanov,
*A category for the adjoint representation*, Section 3,
https://arxiv.org/abs/math/0002060.
-/

public section

namespace TauCeti

open PathAlgebra DoubledQuiver

universe u w

variable (k : Type w) [CommRing k] {V : Type u} (G : SimpleGraph V) [Finite V]
  (c : SkewZigzagParameter k G) (t : ∀ i : V, {j : V // G.Adj i j})

/-! ### The weights of the pairing -/

/-- The unit in the Gram-matrix row indexed by a skew-zigzag basis element. Idempotent and volume
rows have weight one. The row of a dart `d` has the ratio from the return edge `d.symm` to the
chosen edge at its base `d.snd`. -/
def skewZigzagPairingWeight : ZigzagBasisIndex G → kˣ
  | .inl _ => 1
  | .inr (.inl d) => c.ratio d.symm.adj (t d.snd).2
  | .inr (.inr _) => 1

omit [Finite V] in
@[simp]
theorem skewZigzagPairingWeight_inl (i : V) :
    skewZigzagPairingWeight k G c t (.inl i) = 1 := (rfl)

omit [Finite V] in
@[simp]
theorem skewZigzagPairingWeight_inr_inl (d : G.Dart) :
    skewZigzagPairingWeight k G c t (.inr (.inl d)) =
      c.ratio d.symm.adj (t d.snd).2 := (rfl)

omit [Finite V] in
@[simp]
theorem skewZigzagPairingWeight_inr_inr (i : V) :
    skewZigzagPairingWeight k G c t (.inr (.inr i)) = 1 := (rfl)

/-! ### The normalized trace -/

/-- **The Frobenius trace of a skew-zigzag algebra**, normalized by chosen incident edges: it is
one on the chosen volume class at each vertex and zero on the vertex idempotents and arrows. -/
noncomputable def skewZigzagTrace : skewZigzagQuotient k G c →ₗ[k] k :=
  (skewZigzagBasis k G c t).constr k
    (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) fun _ => 1))

/-- The normalized trace on the skew-zigzag basis. -/
theorem skewZigzagTrace_skewZigzagBasisFun (b : ZigzagBasisIndex G) :
    skewZigzagTrace k G c t (skewZigzagBasisFun k G c t b) =
      Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) fun _ => 1) b := by
  rw [← skewZigzagBasis_apply k G c t b]
  exact (skewZigzagBasis k G c t).constr_basis k
    (Sum.elim (fun _ => 0) (Sum.elim (fun _ => 0) fun _ => 1)) b

/-- The normalized trace vanishes on a vertex idempotent. -/
@[simp]
theorem skewZigzagTrace_skewZigzagMk_vertexIdempotent (i : V) :
    skewZigzagTrace k G c t
      (skewZigzagMk k G c (vertexIdempotent k (vertex G i))) = 0 := by
  simpa using skewZigzagTrace_skewZigzagBasisFun k G c t (.inl i)

/-- The normalized trace vanishes on an arrow. -/
@[simp]
theorem skewZigzagTrace_skewZigzagMk_ofArrow (d : G.Dart) :
    skewZigzagTrace k G c t (skewZigzagMk k G c (ofArrow (arrow G d.adj))) = 0 := by
  simpa using skewZigzagTrace_skewZigzagBasisFun k G c t (.inr (.inl d))

/-- The normalized trace is one on the chosen volume class. -/
@[simp]
theorem skewZigzagTrace_skewZigzagVolume_chosen (i : V) :
    skewZigzagTrace k G c t (skewZigzagVolume k G c (t i)) = 1 := by
  simpa using skewZigzagTrace_skewZigzagBasisFun k G c t (.inr (.inr i))

/-- The normalized trace of an arbitrary backtrack is its prescribed ratio to the chosen
backtrack at the same vertex. -/
@[simp]
theorem skewZigzagTrace_skewZigzagVolume {i : V} (e : {j : V // G.Adj i j}) :
    skewZigzagTrace k G c t (skewZigzagVolume k G c e) =
      (c.ratio e.2 (t i).2 : k) := by
  have he := skewZigzagMk_backtrackElem_eq_smul_skewZigzagVolume k G c e e.2
  rw [c.ratio_self, Units.val_one, one_smul] at he
  rw [← he, skewZigzagMk_backtrackElem_eq_smul_skewZigzagVolume k G c (t i) e.2, map_smul,
    skewZigzagTrace_skewZigzagVolume_chosen]
  exact mul_one _

/-! ### The Frobenius pairing -/

/-- **The Frobenius pairing of a skew-zigzag algebra**, `(x, y) ↦ tr (x * y)`. -/
noncomputable def skewZigzagTracePairing :
    LinearMap.BilinForm k (skewZigzagQuotient k G c) :=
  (LinearMap.mul k (skewZigzagQuotient k G c)).compr₂ (skewZigzagTrace k G c t)

@[simp]
theorem skewZigzagTracePairing_apply (x y : skewZigzagQuotient k G c) :
    skewZigzagTracePairing k G c t x y = skewZigzagTrace k G c t (x * y) := (rfl)

/-- **The skew-zigzag trace pairing is associative**: both sides are the trace of the product of
the three arguments. -/
theorem skewZigzagTracePairing_mul_assoc (x y z : skewZigzagQuotient k G c) :
    skewZigzagTracePairing k G c t (x * y) z =
      skewZigzagTracePairing k G c t x (y * z) := by
  rw [skewZigzagTracePairing_apply, skewZigzagTracePairing_apply, mul_assoc]

/-! ### The weighted permutation Gram matrix -/

open scoped Classical in
/-- **The Gram matrix of the skew-zigzag trace pairing is a weighted permutation matrix.** The
only nonzero entry in the row indexed by `b` occurs at `zigzagDualIndex G b`, and its value is the
unit `skewZigzagPairingWeight k G c t b`. -/
theorem skewZigzagTracePairing_skewZigzagBasisFun (b b' : ZigzagBasisIndex G) :
    skewZigzagTracePairing k G c t (skewZigzagBasisFun k G c t b)
        (skewZigzagBasisFun k G c t b') =
      if b' = zigzagDualIndex G b then (skewZigzagPairingWeight k G c t b : k) else 0 := by
  rw [skewZigzagTracePairing_apply]
  rcases b with i | d | i <;> rcases b' with i' | d' | i' <;>
    simp only [skewZigzagBasisFun_inl, skewZigzagBasisFun_inr_inl,
      skewZigzagBasisFun_inr_inr, zigzagDualIndex_inl, zigzagDualIndex_inr_inl,
      zigzagDualIndex_inr_inr, skewZigzagPairingWeight_inl,
      skewZigzagPairingWeight_inr_inl, skewZigzagPairingWeight_inr_inr, Units.val_one]
  · rcases eq_or_ne i i' with rfl | h
    · rw [skewZigzagMk_vertexIdempotent_mul_self,
        skewZigzagTrace_skewZigzagMk_vertexIdempotent]
      simp
    · rw [skewZigzagMk_vertexIdempotent_mul_vertexIdempotent_of_ne k G c h, map_zero]
      simp
  · rcases eq_or_ne i d'.snd with rfl | h
    · rw [skewZigzagMk_vertexIdempotent_mul_ofArrow,
        skewZigzagTrace_skewZigzagMk_ofArrow]
      simp
    · rw [skewZigzagMk_vertexIdempotent_mul_ofArrow_of_ne k G c d' h, map_zero]
      simp
  · rcases eq_or_ne i i' with rfl | h
    · rw [skewZigzagMk_vertexIdempotent_mul_skewZigzagVolume,
        skewZigzagTrace_skewZigzagVolume_chosen]
      simp
    · rw [skewZigzagMk_vertexIdempotent_mul_skewZigzagVolume_of_ne k G c (t i') h,
        map_zero]
      simp [Ne.symm h]
  · rcases eq_or_ne i' d.fst with rfl | h
    · rw [skewZigzagMk_ofArrow_mul_vertexIdempotent,
        skewZigzagTrace_skewZigzagMk_ofArrow]
      simp
    · rw [skewZigzagMk_ofArrow_mul_vertexIdempotent_of_ne k G c d h, map_zero]
      simp
  · rcases eq_or_ne d' d.symm with rfl | h
    · rw [skewZigzagMk_ofArrow_mul_ofArrow_symm,
        skewZigzagTrace_skewZigzagVolume]
      simp
    · rw [skewZigzagMk_ofArrow_mul_ofArrow_of_ne k G c h, map_zero]
      simp [h]
  · rw [skewZigzagMk_ofArrow_mul_skewZigzagVolume, map_zero]
    simp
  · rcases eq_or_ne i' i with rfl | h
    · rw [skewZigzagVolume_mul_skewZigzagMk_vertexIdempotent,
        skewZigzagTrace_skewZigzagVolume_chosen]
      simp
    · rw [skewZigzagVolume_mul_skewZigzagMk_vertexIdempotent_of_ne k G c (t i) h,
        map_zero]
      simp [h]
  · rw [skewZigzagVolume_mul_skewZigzagMk_ofArrow, map_zero]
    simp
  · rw [skewZigzagVolume_mul_skewZigzagVolume, map_zero]
    simp

/-! ### Perfectness -/

/-- **The skew-zigzag trace pairing is perfect.** Its weighted permutation Gram matrix maps the
skew-zigzag basis to a basis of the dual: the weights are units by definition of a skew parameter.
-/
instance skewZigzagTracePairing_isPerfPair :
    (skewZigzagTracePairing k G c t).IsPerfPair := by
  classical
  let _ : Finite G.Dart :=
    Finite.of_injective _ (SimpleGraph.Dart.toProd_injective (G := G))
  let B := skewZigzagBasis k G c t
  let _ : Module.Finite k (skewZigzagQuotient k G c) := Module.Finite.of_basis B
  let _ : Module.Free k (skewZigzagQuotient k G c) := Module.Free.of_basis B
  let w := skewZigzagPairingWeight k G c t
  let ι := (zigzagDualIndex_involutive G).toPerm
  have hleft : skewZigzagTracePairing k G c t =
      (B.equiv (B.dualBasis.unitsSMul fun b ↦ w (ι b)) ι).toLinearMap := by
    refine B.ext fun b ↦ B.ext fun b' ↦ ?_
    dsimp only [B]
    rw [LinearEquiv.coe_coe, Module.Basis.equiv_apply, Module.Basis.unitsSMul_apply,
      LinearMap.smul_apply, Module.Basis.dualBasis_apply_self, skewZigzagBasis_apply,
      skewZigzagBasis_apply, skewZigzagTracePairing_skewZigzagBasisFun]
    dsimp only [w, ι]
    simp only [Function.Involutive.coe_toPerm]
    by_cases h : b' = zigzagDualIndex G b
    · subst b'
      simp only [zigzagDualIndex_zigzagDualIndex, Units.smul_def, smul_eq_mul, mul_one,
        ↓reduceIte]
    · simp only [h, smul_zero, ↓reduceIte]
  apply LinearMap.IsPerfPair.of_bijective
  rw [hleft]
  exact LinearEquiv.bijective _

/-- **The skew-zigzag trace pairing is nondegenerate.** This follows from its perfectness, which is
the stronger assertion over a general commutative ring. -/
theorem skewZigzagTracePairing_nondegenerate :
    (skewZigzagTracePairing k G c t).Nondegenerate :=
  LinearMap.IsPerfPair.nondegenerate inferInstance

/-! ### Symmetry -/

/-- The chosen skew-zigzag trace is a trace exactly when the Gram weights of each dart and its
reverse agree. This is the precise obstruction to symmetry; idempotent-volume pairs are already
symmetric and all other products have zero trace. -/
theorem skewZigzagTracePairing_isSymm_iff :
    (skewZigzagTracePairing k G c t).IsSymm ↔
      ∀ d : G.Dart,
        c.ratio d.symm.adj (t d.snd).2 = c.ratio d.adj (t d.fst).2 := by
  constructor
  · intro h d
    have hd := h.eq
      (skewZigzagBasisFun k G c t (.inr (.inl d)))
      (skewZigzagBasisFun k G c t (.inr (.inl d.symm)))
    rw [skewZigzagTracePairing_skewZigzagBasisFun,
      skewZigzagTracePairing_skewZigzagBasisFun] at hd
    apply Units.ext
    simp only [zigzagDualIndex_inr_inl, skewZigzagPairingWeight_inr_inl,
      SimpleGraph.Dart.symm_symm, ↓reduceIte] at hd
    exact hd
  · intro h
    rw [LinearMap.BilinForm.isSymm_iff_basis (skewZigzagBasis k G c t)]
    intro b b'
    rw [skewZigzagBasis_apply, skewZigzagBasis_apply,
      skewZigzagTracePairing_skewZigzagBasisFun,
      skewZigzagTracePairing_skewZigzagBasisFun]
    have hweight : skewZigzagPairingWeight k G c t b =
        skewZigzagPairingWeight k G c t (zigzagDualIndex G b) := by
      rcases b with i | d | i
      · rw [zigzagDualIndex_inl, skewZigzagPairingWeight_inl,
          skewZigzagPairingWeight_inr_inr]
      · rw [zigzagDualIndex_inr_inl, skewZigzagPairingWeight_inr_inl,
          skewZigzagPairingWeight_inr_inl]
        change c.ratio d.symm.adj (t d.snd).2 = c.ratio d.adj (t d.fst).2
        exact h d
      · rw [zigzagDualIndex_inr_inr, skewZigzagPairingWeight_inr_inr,
          skewZigzagPairingWeight_inl]
    by_cases hb : b' = zigzagDualIndex G b
    · subst b'
      simp only [zigzagDualIndex_zigzagDualIndex, ↓reduceIte]
      exact congrArg Units.val hweight
    · have hb' : b ≠ zigzagDualIndex G b' := by
        intro hdual
        apply hb
        calc
          b' = zigzagDualIndex G (zigzagDualIndex G b') :=
            (zigzagDualIndex_zigzagDualIndex G b').symm
          _ = zigzagDualIndex G b := congrArg (zigzagDualIndex G) hdual.symm
      simp only [hb, hb', ↓reduceIte]

/-- The chosen skew-zigzag trace is a trace exactly when the Gram weights of each dart and its
reverse agree. -/
theorem skewZigzagTrace_mul_comm_iff :
    (∀ x y : skewZigzagQuotient k G c,
      skewZigzagTrace k G c t (x * y) = skewZigzagTrace k G c t (y * x)) ↔
      ∀ d : G.Dart,
        c.ratio d.symm.adj (t d.snd).2 = c.ratio d.adj (t d.fst).2 := by
  rw [← skewZigzagTracePairing_isSymm_iff]
  constructor
  · exact fun h ↦ ⟨fun x y ↦ h x y⟩
  · exact fun h x y ↦ h.eq x y

/-- If opposite darts have equal pairing weights, the skew-zigzag trace pairing is symmetric. -/
theorem skewZigzagTracePairing_isSymm
    (h : ∀ d : G.Dart,
      c.ratio d.symm.adj (t d.snd).2 = c.ratio d.adj (t d.fst).2) :
    (skewZigzagTracePairing k G c t).IsSymm :=
  (skewZigzagTracePairing_isSymm_iff k G c t).2 h

/-- If opposite darts have equal pairing weights, the normalized functional is a trace. -/
theorem skewZigzagTrace_mul_comm
    (h : ∀ d : G.Dart,
      c.ratio d.symm.adj (t d.snd).2 = c.ratio d.adj (t d.fst).2)
    (x y : skewZigzagQuotient k G c) :
    skewZigzagTrace k G c t (x * y) = skewZigzagTrace k G c t (y * x) :=
  (skewZigzagTrace_mul_comm_iff k G c t).2 h x y

end TauCeti
