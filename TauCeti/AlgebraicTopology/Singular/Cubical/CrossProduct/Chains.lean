/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.CrossProduct
public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalized
import Mathlib.LinearAlgebra.BilinearMap

/-!
# The cross product of cubical chains

The cross product of singular cubes (`TauCeti.SingularCube.crossProduct`) extends bilinearly to
cubical chains,
`CubicalChain X R p →ₗ[R] CubicalChain Y R q →ₗ[R] CubicalChain (X × Y) R (p + q)`.  It is natural
in both spaces, and it sends degenerate chains to degenerate chains in each variable, so it
descends to the normalized chains.  The boundary is a derivation for it, with the Koszul sign:
`∂ (a × b) = ∂ a × b + (-1) ^ p • (a × ∂ b)` for `a` of degree `p`.

The boundary `CubicalChain.boundary X R n` is defined on `(n + 1)`-chains, so the Leibniz rule is
stated for factors of positive degree `p + 1` and `q + 1`, where the product has degree
`(p + 1) + (q + 1) = (p + q + 1) + 1` after the reindexing `CubicalChain.cast`; the two cases where
a factor has degree `0` are stated separately.

## Main definitions

* `TauCeti.CubicalChain.crossProduct X Y R p q`: the cross product of cubical chains.
* `TauCeti.NormalizedCubicalChain.crossProduct X Y R p q`: the cross product of normalized chains.

## Main results

* `TauCeti.CubicalChain.crossProduct_single`: the cross product of two cubes.
* `TauCeti.CubicalChain.map_crossProduct`: naturality.
* `TauCeti.CubicalChain.crossProduct_left_mem_degenerate`,
  `TauCeti.CubicalChain.crossProduct_right_mem_degenerate`: degenerate chains go to degenerate
  chains, so the product descends to `TauCeti.NormalizedCubicalChain.crossProduct`.
* `TauCeti.CubicalChain.boundary_crossProduct`: the Leibniz rule, with
  `boundary_crossProduct_zero_left` and `boundary_crossProduct_zero_right` for a factor of
  degree `0`.
* `TauCeti.NormalizedCubicalChain.boundary_crossProduct`: the Leibniz rule on normalized chains,
  with `boundary_crossProduct_zero_left` and `boundary_crossProduct_zero_right`.

## References

* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter VII.
-/

public section

noncomputable section

open Finsupp unitInterval

namespace TauCeti

variable {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [TopologicalSpace W]

namespace CubicalChain

section CrossProduct

variable {p q : ℕ} (R : Type*) [CommSemiring R]

variable (X Y) in
/-- The **cross product of cubical chains**, the bilinear extension of the cross product of
singular cubes. -/
def crossProduct (p q : ℕ) :
    CubicalChain X R p →ₗ[R] CubicalChain Y R q →ₗ[R] CubicalChain (X × Y) R (p + q) :=
  Finsupp.lift (CubicalChain Y R q →ₗ[R] CubicalChain (X × Y) R (p + q)) R (SingularCube X p)
    fun c ↦ lmapDomain R R (SingularCube.crossProduct c)

/-- The cross product of two cubes with coefficients. -/
@[simp]
theorem crossProduct_single (c : SingularCube X p) (d : SingularCube Y q) (a b : R) :
    crossProduct X Y R p q (single c a) (single d b) =
      single (SingularCube.crossProduct c d) (a * b) := by
  simp [crossProduct, smul_single]

/-- The cross product of chains is natural in both spaces. -/
theorem map_crossProduct (f : C(X, Z)) (g : C(Y, W)) (a : CubicalChain X R p)
    (b : CubicalChain Y R q) :
    map R (f.prodMap g) (p + q) (crossProduct X Y R p q a b) =
      crossProduct Z W R p q (map R f p a) (map R g q b) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a a' ha ha' => simp [ha, ha']
  | single c r =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b b' hb hb' => simp [hb, hb']
    | single d s => simp [SingularCube.crossProduct_comp]

/-- The cross product of a degenerate chain with any chain is degenerate. -/
theorem crossProduct_left_mem_degenerate {a : CubicalChain X R p} (ha : a ∈ degenerate X R p)
    (b : CubicalChain Y R q) : crossProduct X Y R p q a b ∈ degenerate (X × Y) R (p + q) := by
  rw [degenerate_def] at ha
  induction ha using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨c, hc, rfl⟩ := hf
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b b' hb hb' => simpa using add_mem hb hb'
    | single d s =>
      rw [crossProduct_single]
      exact single_mem_degenerate R
        ((SingularCube.isDegenerate_crossProduct_iff c d).2 (Or.inl hc)) _
  | zero => simp
  | add a a' _ _ ha ha' => simpa using add_mem ha ha'
  | smul r a _ ha => simpa using Submodule.smul_mem _ r ha

/-- The cross product of any chain with a degenerate chain is degenerate. -/
theorem crossProduct_right_mem_degenerate (a : CubicalChain X R p) {b : CubicalChain Y R q}
    (hb : b ∈ degenerate Y R q) : crossProduct X Y R p q a b ∈ degenerate (X × Y) R (p + q) := by
  rw [degenerate_def] at hb
  induction hb using Submodule.span_induction with
  | mem f hf =>
    obtain ⟨d, hd, rfl⟩ := hf
    induction a using Finsupp.induction_linear with
    | zero => simp
    | add a a' ha ha' => simpa using add_mem ha ha'
    | single c r =>
      rw [crossProduct_single]
      exact single_mem_degenerate R
        ((SingularCube.isDegenerate_crossProduct_iff c d).2 (Or.inr hd)) _
  | zero => simp
  | add b b' _ _ hb hb' => simpa using add_mem hb hb'
  | smul r b _ hb => simpa using Submodule.smul_mem _ r hb

end CrossProduct

section Leibniz

variable {p q : ℕ} (R : Type*) [CommRing R]

/-- **The Leibniz rule for cubes**: the boundary of the cross product of a `(p + 1)`-cube and a
`(q + 1)`-cube is the sum of the cross products of the boundary of the first factor with the
second, and of the first factor with the boundary of the second, with the sign `(-1) ^ (p + 1)`. -/
theorem boundaryCube_crossProduct (c : SingularCube X (p + 1)) (d : SingularCube Y (q + 1)) :
    boundaryCube R (SingularCube.cast (by omega : (p + 1) + (q + 1) = (p + q + 1) + 1)
        (SingularCube.crossProduct c d)) =
      crossProduct X Y R p (q + 1) (boundaryCube R c) (single d 1) +
        (-1 : R) ^ (p + 1) • cast R (by omega : (p + 1) + q = p + q + 1)
          (crossProduct X Y R (p + 1) q (single c 1) (boundaryCube R d)) := by
  have h : (p + 1) + (q + 1) = (p + q + 1) + 1 := by omega
  have h' : (p + 1) + q = p + q + 1 := by omega
  -- Split the sum over the faces into the two coordinate blocks.
  have hsum : ∀ F : Fin (p + q + 1 + 1) → CubicalChain (X × Y) R (p + q + 1),
      ∑ k, F k = ∑ i : Fin (p + 1), F (Fin.cast h (i.castAdd (q + 1))) +
        ∑ j : Fin (q + 1), F (Fin.cast h (j.natAdd (p + 1))) := fun F ↦ by
    rw [← Fin.sum_univ_add (fun k : Fin ((p + 1) + (q + 1)) ↦ F (Fin.cast h k))]
    exact (Fintype.sum_equiv (finCongr h) _ _ fun _ ↦ rfl).symm
  have hA : ∀ (i : Fin (p + 1)) (t : I),
      SingularCube.face (Fin.cast h (i.castAdd (q + 1))) t
          (SingularCube.cast h (SingularCube.crossProduct c d)) =
        SingularCube.crossProduct (SingularCube.face i t c) d := fun i t ↦
    SingularCube.face_crossProduct_castAdd c d i t
  have hB : ∀ (j : Fin (q + 1)) (t : I),
      SingularCube.face (Fin.cast h (j.natAdd (p + 1))) t
          (SingularCube.cast h (SingularCube.crossProduct c d)) =
        SingularCube.cast h' (SingularCube.crossProduct c (SingularCube.face j t d)) := fun j t ↦ by
    rw [← SingularCube.face_crossProduct_natAdd (p := p + 1) c d j t]
    exact SingularCube.face_cast h' (j.natAdd (p + 1)) t
      (SingularCube.crossProduct (p := p + 1) (q := q + 1) c d)
  rw [boundaryCube_def, hsum]
  simp only [hA, hB, boundaryCube_def, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    map_sub, LinearMap.sub_apply, crossProduct_single, mul_one, cast_single, Finset.smul_sum,
    smul_sub, smul_smul, pow_add, Fin.val_cast, Fin.val_natAdd, Fin.val_castAdd]

/-- **The Leibniz rule for cubical chains**: for `a` of degree `p + 1` and `b` of degree `q + 1`,
`∂ (a × b) = ∂ a × b + (-1) ^ (p + 1) • (a × ∂ b)`, in degree `p + q + 1`. -/
theorem boundary_crossProduct (a : CubicalChain X R (p + 1)) (b : CubicalChain Y R (q + 1)) :
    boundary (X × Y) R (p + q + 1)
        (cast R (by omega : (p + 1) + (q + 1) = (p + q + 1) + 1)
          (crossProduct X Y R (p + 1) (q + 1) a b)) =
      crossProduct X Y R p (q + 1) (boundary X R p a) b +
        (-1 : R) ^ (p + 1) • cast R (by omega : (p + 1) + q = p + q + 1)
          (crossProduct X Y R (p + 1) q a (boundary Y R q b)) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a a' ha ha' =>
    simp only [map_add, LinearMap.add_apply, smul_add, ha, ha']
    abel
  | single c r =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b b' hb hb' =>
      simp only [map_add, smul_add, hb, hb']
      abel
    | single d s =>
      rw [← smul_single_one c r, ← smul_single_one d s]
      simp only [map_smul, LinearMap.smul_apply, crossProduct_single, cast_single,
        boundary_single_one, mul_one, boundaryCube_crossProduct, smul_add, smul_comm s r]
      congr 1
      rw [smul_comm s ((-1 : R) ^ (p + 1)), smul_comm r ((-1 : R) ^ (p + 1))]

/-- The Leibniz rule for cubes when the second factor is a point. -/
theorem boundaryCube_crossProduct_zero_right (c : SingularCube X (p + 1))
    (d : SingularCube Y 0) :
    boundaryCube R (n := p) (SingularCube.crossProduct (p := p + 1) (q := 0) c d) =
      crossProduct X Y R p 0 (boundaryCube R c) (single d 1) := by
  have hA : ∀ (i : Fin (p + 1)) (t : I),
      SingularCube.face i t (SingularCube.crossProduct (p := p + 1) (q := 0) c d) =
        SingularCube.crossProduct (SingularCube.face i t c) d := fun i t ↦ by
    apply ContinuousMap.ext
    intro x
    rw [SingularCube.crossProduct_zero_right (SingularCube.face i t c) d x]
    simp only [SingularCube.face_apply, ↓SingularCube.crossProduct_apply, Fin.castAdd_zero,
      Fin.cast_eq_self, Nat.add_zero, Fin.cast_refl, CompTriple.comp_eq, Prod.mk.injEq,
      true_and]
    exact congrArg d (Subsingleton.elim _ _)
  simp only [boundaryCube_def, hA, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    map_sub, LinearMap.sub_apply, crossProduct_single, mul_one]

/-- The Leibniz rule for cubes when the first factor is a point. -/
theorem boundaryCube_crossProduct_zero_left (c : SingularCube X 0) (d : SingularCube Y (q + 1)) :
    boundaryCube R (SingularCube.cast (by omega : 0 + (q + 1) = q + 1)
        (SingularCube.crossProduct c d)) =
      cast R (by omega : 0 + q = q) (crossProduct X Y R 0 q (single c 1) (boundaryCube R d)) := by
  have h' : 0 + q = q := by omega
  have hB : ∀ (k : Fin (q + 1)) (t : I),
      SingularCube.face k t (SingularCube.cast (by omega : 0 + (q + 1) = q + 1)
          (SingularCube.crossProduct c d)) =
        SingularCube.cast h' (SingularCube.crossProduct c (SingularCube.face k t d)) := fun k t ↦ by
    have := SingularCube.face_cast h' (k.natAdd 0) t
      (SingularCube.crossProduct (p := 0) (q := q + 1) c d)
    rw [SingularCube.face_crossProduct_natAdd] at this
    convert this using 2
    exact Fin.ext (by simp)
  simp only [boundaryCube_def, hB, map_sum, map_smul, map_sub, crossProduct_single, mul_one,
    cast_single]

/-- The Leibniz rule for chains when the second factor has degree `0`. -/
theorem boundary_crossProduct_zero_right (a : CubicalChain X R (p + 1))
    (b : CubicalChain Y R 0) :
    boundary (X × Y) R p (crossProduct X Y R (p + 1) 0 a b) =
      crossProduct X Y R p 0 (boundary X R p a) b := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | single c r =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b b' hb hb' => simp only [map_add, hb, hb']
    | single d s =>
      rw [← smul_single_one c r, ← smul_single_one d s]
      simp only [map_smul, LinearMap.smul_apply, crossProduct_single, boundary_single_one, mul_one,
        boundaryCube_crossProduct_zero_right]

/-- The Leibniz rule for chains when the first factor has degree `0`. -/
theorem boundary_crossProduct_zero_left (a : CubicalChain X R 0) (b : CubicalChain Y R (q + 1)) :
    boundary (X × Y) R q (cast R (by omega : 0 + (q + 1) = q + 1)
        (crossProduct X Y R 0 (q + 1) a b)) =
      cast R (by omega : 0 + q = q) (crossProduct X Y R 0 q a (boundary Y R q b)) := by
  induction a using Finsupp.induction_linear with
  | zero => simp
  | add a a' ha ha' => simp only [map_add, LinearMap.add_apply, ha, ha']
  | single c r =>
    induction b using Finsupp.induction_linear with
    | zero => simp
    | add b b' hb hb' => simp only [map_add, hb, hb']
    | single d s =>
      rw [← smul_single_one c r, ← smul_single_one d s]
      simp only [map_smul, LinearMap.smul_apply, crossProduct_single, cast_single,
        boundary_single_one, mul_one, boundaryCube_crossProduct_zero_left]

end Leibniz

end CubicalChain

namespace NormalizedCubicalChain

open CubicalChain

variable (R : Type*) [CommRing R]

variable (X Y) in
/-- The **cross product of normalized cubical chains**, induced by the cross product of the
unnormalized chains, since degenerate chains go to degenerate chains in each variable. -/
def crossProduct (p q : ℕ) :
    NormalizedCubicalChain X R p →ₗ[R] NormalizedCubicalChain Y R q →ₗ[R]
      NormalizedCubicalChain (X × Y) R (p + q) :=
  (degenerate X R p).liftQ
    (((degenerate Y R q).liftQ
      (LinearMap.flip (LinearMap.compr₂ (CubicalChain.crossProduct X Y R p q)
        (Submodule.mkQ (degenerate (X × Y) R (p + q)))))
      fun b hb ↦ LinearMap.mem_ker.2 (LinearMap.ext fun a ↦ (Submodule.Quotient.mk_eq_zero _).2
        (crossProduct_right_mem_degenerate R a hb))).flip)
    fun a ha ↦ LinearMap.mem_ker.2 (LinearMap.ext fun b ↦ by
      induction b using Submodule.Quotient.induction_on with
      | H b => exact (Submodule.Quotient.mk_eq_zero _).2 (crossProduct_left_mem_degenerate R ha b))

/-- The cross product of the classes of two chains is the class of their cross product. -/
@[simp]
theorem crossProduct_mk {p q : ℕ} (a : CubicalChain X R p) (b : CubicalChain Y R q) :
    crossProduct X Y R p q (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) =
      Submodule.Quotient.mk (CubicalChain.crossProduct X Y R p q a b) := by
  rw [crossProduct, Submodule.liftQ_apply, LinearMap.flip_apply, Submodule.liftQ_apply,
    LinearMap.flip_apply, LinearMap.compr₂_apply, Submodule.mkQ_apply]

/-- The cross product of the classes of two cubes is the class of their cross product. -/
@[simp]
theorem crossProduct_ofCube {p q : ℕ} (c : SingularCube X p) (d : SingularCube Y q) :
    crossProduct X Y R p q (ofCube X R c) (ofCube Y R d) =
      ofCube (X × Y) R (SingularCube.crossProduct c d) := by
  rw [ofCube_def, ofCube_def, ofCube_def, crossProduct_mk, CubicalChain.crossProduct_single,
    mul_one]

/-- The cross product of normalized chains is natural in both spaces. -/
theorem map_crossProduct {p q : ℕ} (f : C(X, Z)) (g : C(Y, W)) (a : NormalizedCubicalChain X R p)
    (b : NormalizedCubicalChain Y R q) :
    map R (f.prodMap g) (p + q) (crossProduct X Y R p q a b) =
      crossProduct Z W R p q (map R f p a) (map R g q b) := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b => simp [CubicalChain.map_crossProduct]

/-- **The Leibniz rule for normalized cubical chains**: for `a` of degree `p + 1` and `b` of degree
`q + 1`, `∂ (a × b) = ∂ a × b + (-1) ^ (p + 1) • (a × ∂ b)`, in degree `p + q + 1`. -/
theorem boundary_crossProduct {p q : ℕ} (a : NormalizedCubicalChain X R (p + 1))
    (b : NormalizedCubicalChain Y R (q + 1)) :
    boundary (X × Y) R (p + q + 1)
        (cast R (by omega : (p + 1) + (q + 1) = (p + q + 1) + 1)
          (crossProduct X Y R (p + 1) (q + 1) a b)) =
      crossProduct X Y R p (q + 1) (boundary X R p a) b +
        (-1 : R) ^ (p + 1) • cast R (by omega : (p + 1) + q = p + q + 1)
          (crossProduct X Y R (p + 1) q a (boundary Y R q b)) := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b =>
      simp only [crossProduct_mk, boundary_mk, cast_mk, CubicalChain.boundary_crossProduct,
        Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul]

/-- The Leibniz rule for normalized chains when the second factor has degree `0`. -/
theorem boundary_crossProduct_zero_right {p : ℕ} (a : NormalizedCubicalChain X R (p + 1))
    (b : NormalizedCubicalChain Y R 0) :
    boundary (X × Y) R p (crossProduct X Y R (p + 1) 0 a b) =
      crossProduct X Y R p 0 (boundary X R p a) b := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b =>
      simp only [crossProduct_mk, boundary_mk, CubicalChain.boundary_crossProduct_zero_right]

/-- The Leibniz rule for normalized chains when the first factor has degree `0`. -/
theorem boundary_crossProduct_zero_left {q : ℕ} (a : NormalizedCubicalChain X R 0)
    (b : NormalizedCubicalChain Y R (q + 1)) :
    boundary (X × Y) R q (cast R (by omega : 0 + (q + 1) = q + 1)
        (crossProduct X Y R 0 (q + 1) a b)) =
      cast R (by omega : 0 + q = q) (crossProduct X Y R 0 q a (boundary Y R q b)) := by
  induction a using Submodule.Quotient.induction_on with
  | H a =>
    induction b using Submodule.Quotient.induction_on with
    | H b =>
      simp only [crossProduct_mk, boundary_mk, cast_mk,
        CubicalChain.boundary_crossProduct_zero_left]

end NormalizedCubicalChain

end TauCeti

end
