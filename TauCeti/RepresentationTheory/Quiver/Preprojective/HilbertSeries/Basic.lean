/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Admissible
public import TauCeti.RepresentationTheory.Quiver.Preprojective.KoszulComplex

/-!
# The matrix Hilbert series of a preprojective algebra

Let `Q` be a finite quiver and `Π = Π_k(Q)` its preprojective algebra over a field `k`. For vertices
`i` and `j` and a degree `n`, the graded corner `e_j Π_n e_i` (`TauCeti.preprojectiveCorner`) is the
span of the classes of the paths of length `n` from `i` to `j` in the doubled quiver. Its dimensions
form the matrix Hilbert series

```text
H(t)_{j,i} = ∑_n dim (e_j Π_n e_i) tⁿ        (TauCeti.preprojectiveHilbertSeries).
```

Restricting the Koszul complex of the vertex module `S_v` (see
`TauCeti.RepresentationTheory.Quiver.Preprojective.KoszulComplex`) to degree `m + 2` and cutting it
down on the right by `e_i` gives the sequence

```text
0 ⟶ K_m(i, v) ⟶ e_v Π_m e_i ⟶ ⨁_{b : w ⟶ v} e_w Π_{m+1} e_i ⟶ e_v Π_{m+2} e_i ⟶ 0,
```

where `K_m(i, v)` is the space of `y ∈ e_v Π_m e_i` killed by the reverse `b*` of every arrow `b`
of the doubled quiver into `v`. It is exact by the exactness of the Koszul complex at its two
right-hand terms, which holds for every quiver. Counting dimensions gives the **Koszul defect
formula** (`TauCeti.finrank_preprojectiveCorner_add_two_add_finrank_preprojectiveCorner`)

```text
dim e_v Π_{m+2} e_i + dim e_v Π_m e_i = ∑_w #(w ⟶ v) dim e_w Π_{m+1} e_i + dim K_m(i, v),
```

together with `dim e_j Π_0 e_i = δ_{ij}` and `dim e_j Π_1 e_i = #(i ⟶ j)`. In matrix form, with `A`
the arrow-count matrix of the doubled quiver and `K(t)` the matrix of the series
`∑_m dim K_m(i, v) tᵐ`, this reads `((1 + t²) I - t A) H(t) = I + t² K(t)`. Consequently
(`TauCeti.mul_preprojectiveHilbertSeries_eq_one_iff`) the **Hilbert series identity**

```text
((1 + t²) I - t A) H(t) = I
```

holds exactly when the left-hand map `y ↦ (ε_b b* y)_b` of every Koszul complex is injective, that
is, exactly when these complexes are projective resolutions of the vertex modules. This is the
form in which Etingof and Eu relate the Koszulity of `Π` to its Hilbert series
`H(t) = ((1 + t²) I - t A)⁻¹`, which they establish for connected non-Dynkin quivers; this file
proves the equivalence for every finite quiver, not the injectivity itself. When `Q` is an
orientation of a simple graph, `(1 + t²) I - t A` is the graded Cartan matrix `(1 + q²) I + q A` of
the zigzag algebra of that graph evaluated at `q = -t`.

## Main definitions

* `TauCeti.preprojectiveCorner`: the graded corner `e_j Π_n e_i`.
* `TauCeti.preprojectiveHilbertSeries`: the matrix Hilbert series of `Π`.

## Main results

* `TauCeti.mem_preprojectiveCorner_iff` and
  `TauCeti.preprojectiveCorner_eq_cornerSubmodule_inf_preprojectiveGrade`: the graded corner is the
  intersection of the degree-`n` piece with the corner `e_j Π e_i`.
* `TauCeti.finrank_preprojectiveCorner_zero` and `TauCeti.finrank_preprojectiveCorner_one`: the
  dimensions in degrees `0` and `1`.
* `TauCeti.finrank_preprojectiveCorner_add_two_add_finrank_preprojectiveCorner`: **the Koszul
  defect formula.**
* `TauCeti.sum_card_mul_finrank_preprojectiveCorner_eq_iff`: the dimension recursion holds in
  degree `m + 2` exactly when the Koszul complex is exact at its left end in degree `m`.
* `TauCeti.mul_preprojectiveHilbertSeries_eq_one_iff`: **the Hilbert series identity
  `((1 + t²) I - t A) H(t) = I` holds exactly when every Koszul complex is a resolution.**

## References

* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Sections 2 and 3.
* D. J. Anick, *Non-commutative graded algebras and their Hilbert series*, J. Algebra 78 (1982).
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

section Corner

variable (k : Type w) (Q : Type u) [CommRing k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- **The graded corner `e_j Π_n e_i`** of the preprojective algebra: the span of the classes of the
paths of length `n` from `i` to `j` in the doubled quiver. By `TauCeti.mem_preprojectiveCorner_iff`
it is the intersection of the degree-`n` piece `TauCeti.preprojectiveGrade` with the corner of the
two vertex idempotents. -/
noncomputable def preprojectiveCorner (n : ℕ) (i j : Symmetrify Q) :
    Submodule k (preprojectiveAlgebra k Q) :=
  (pathsBetween k n i j).map (preprojectiveMk k Q).toLinearMap

variable {k Q}

/-- The class of a vertex idempotent is idempotent. -/
private theorem preprojectiveMk_vertexIdempotent_mul_self (i : Symmetrify Q) :
    preprojectiveMk k Q (vertexIdempotent k i) * preprojectiveMk k Q (vertexIdempotent k i) =
      preprojectiveMk k Q (vertexIdempotent k i) := by
  rw [← map_mul, vertexIdempotent_mul_self]

/-- **The graded corner `e_j Π_n e_i` is the degree-`n` part of the corner `e_j Π e_i`.** -/
theorem mem_preprojectiveCorner_iff {n : ℕ} {i j : Symmetrify Q} {x : preprojectiveAlgebra k Q} :
    x ∈ preprojectiveCorner k Q n i j ↔ x ∈ preprojectiveGrade k Q n ∧
      preprojectiveMk k Q (vertexIdempotent k j) * x * preprojectiveMk k Q (vertexIdempotent k i) =
        x := by
  simp only [preprojectiveCorner, Submodule.mem_map, AlgHom.toLinearMap_apply]
  constructor
  · rintro ⟨p, hp, rfl⟩
    rw [mem_pathsBetween_iff] at hp
    exact ⟨preprojectiveMk_mem_preprojectiveGrade k Q hp.1, by rw [← map_mul, ← map_mul, hp.2]⟩
  · rintro ⟨hx, hc⟩
    obtain ⟨y, hy, rfl⟩ := (mem_preprojectiveGrade_iff k Q).1 hx
    refine ⟨vertexIdempotent k j * y * vertexIdempotent k i, mem_pathsBetween_iff.2 ⟨?_, ?_⟩,
      by rw [map_mul, map_mul, hc]⟩
    · simpa using SetLike.mul_mem_graded (SetLike.mul_mem_graded
        (vertexIdempotent_mem_grade_zero (k := k) j) hy)
        (vertexIdempotent_mem_grade_zero (k := k) i)
    · rw [← mul_assoc, ← mul_assoc, vertexIdempotent_mul_self, mul_assoc _ _ (vertexIdempotent k i),
        vertexIdempotent_mul_self]

/-- **The graded corner as an intersection**: `e_j Π_n e_i` is the corner submodule of the two
vertex idempotents intersected with the degree-`n` piece. -/
theorem preprojectiveCorner_eq_cornerSubmodule_inf_preprojectiveGrade (n : ℕ)
    (i j : Symmetrify Q) :
    preprojectiveCorner k Q n i j =
      cornerSubmodule k (preprojectiveMk k Q (vertexIdempotent k j))
          (preprojectiveMk k Q (vertexIdempotent k i)) ⊓ preprojectiveGrade k Q n := by
  ext x
  rw [mem_preprojectiveCorner_iff, Submodule.mem_inf,
    mem_cornerSubmodule_iff k (preprojectiveMk_vertexIdempotent_mul_self j)
      (preprojectiveMk_vertexIdempotent_mul_self i), and_comm]

/-- An element of `e_j Π_n e_i` is fixed by left multiplication by `e_j`. -/
theorem preprojectiveMk_vertexIdempotent_mul_of_mem_preprojectiveCorner {n : ℕ}
    {i j : Symmetrify Q} {x : preprojectiveAlgebra k Q} (hx : x ∈ preprojectiveCorner k Q n i j) :
    preprojectiveMk k Q (vertexIdempotent k j) * x = x := by
  obtain ⟨-, hc⟩ := mem_preprojectiveCorner_iff.1 hx
  rw [← hc, ← mul_assoc, ← mul_assoc, preprojectiveMk_vertexIdempotent_mul_self]

/-- An element of `e_j Π_n e_i` is fixed by right multiplication by `e_i`. -/
theorem mul_preprojectiveMk_vertexIdempotent_of_mem_preprojectiveCorner {n : ℕ}
    {i j : Symmetrify Q} {x : preprojectiveAlgebra k Q} (hx : x ∈ preprojectiveCorner k Q n i j) :
    x * preprojectiveMk k Q (vertexIdempotent k i) = x := by
  obtain ⟨-, hc⟩ := mem_preprojectiveCorner_iff.1 hx
  rw [← hc, mul_assoc, preprojectiveMk_vertexIdempotent_mul_self]

/-- Left multiplication by an arrow `b : j ⟶ l` of the doubled quiver maps `e_j Π_n e_i` into
`e_l Π_{n+1} e_i`. -/
theorem preprojectiveMk_ofArrow_mul_mem_preprojectiveCorner {n : ℕ} {i j l : Symmetrify Q}
    (b : j ⟶ l) {x : preprojectiveAlgebra k Q} (hx : x ∈ preprojectiveCorner k Q n i j) :
    preprojectiveMk k Q (ofArrow b) * x ∈ preprojectiveCorner k Q (n + 1) i l := by
  obtain ⟨hxn, -⟩ := mem_preprojectiveCorner_iff.1 hx
  refine mem_preprojectiveCorner_iff.2 ⟨?_, ?_⟩
  · rw [add_comm]
    exact mul_mem_preprojectiveGrade k Q
      (preprojectiveMk_mem_preprojectiveGrade k Q (ofArrow_mem_grade_one b)) hxn
  · rw [mul_assoc, mul_assoc (preprojectiveMk k Q (ofArrow b)),
      mul_preprojectiveMk_vertexIdempotent_of_mem_preprojectiveCorner hx, ← mul_assoc, ← map_mul,
      ofArrow_eq_ofPath, vertexIdempotent_mul_ofPath]

end Corner

/-- The sign `ε_b = ±1` of an arrow of the doubled quiver is nonzero. -/
private theorem doubledArrowSign_ne_zero (k : Type w) {Q : Type u} [Field k] [Quiver.{v} Q]
    {i j : Symmetrify Q} (b : i ⟶ j) : doubledArrowSign k b ≠ 0 := by
  rcases b with a | a
  · exact (doubledArrowSign_inl k a).trans_ne one_ne_zero
  · exact (doubledArrowSign_inr k a).trans_ne (neg_ne_zero.2 one_ne_zero)

section Field

variable (k : Type w) {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

/-- The graded corners of the preprojective algebra of a finite quiver are finite-dimensional:
there are finitely many paths of each length between two vertices. -/
instance (n : ℕ) (i j : Symmetrify Q) : FiniteDimensional k (preprojectiveCorner k Q n i j) :=
  Module.Finite.map _ _

attribute [local instance] preprojectiveGradedAlgebra

/-- Left multiplication by an arrow shifts the homogeneous components by one. -/
private theorem preprojectiveMk_ofArrow_mul_decompose {i j : Symmetrify Q} (b : i ⟶ j)
    (y : preprojectiveAlgebra k Q) (m : ℕ) :
    preprojectiveMk k Q (ofArrow b) *
        (DirectSum.decompose (preprojectiveGrade k Q) y m : preprojectiveAlgebra k Q) =
      DirectSum.decompose (preprojectiveGrade k Q) (preprojectiveMk k Q (ofArrow b) * y)
        (m + 1) := by
  rw [DirectSum.coe_decompose_mul_of_left_mem_of_le _
    (preprojectiveMk_mem_preprojectiveGrade k Q (ofArrow_mem_grade_one b)) (by omega : 1 ≤ m + 1),
    Nat.add_sub_cancel]

/-- The degree-zero component of a scalar multiple of an arrow multiple vanishes. -/
private theorem decompose_smul_ofArrow_mul_zero {i j : Symmetrify Q}
    (c : k) (b : i ⟶ j) (y : preprojectiveAlgebra k Q) :
    (DirectSum.decompose (preprojectiveGrade k Q)
        (c • (preprojectiveMk k Q (ofArrow b) * y)) 0 :
      preprojectiveAlgebra k Q) = 0 := by
  rw [DirectSum.decompose_smul, DirectSum.smul_apply, Submodule.coe_smul,
    DirectSum.coe_decompose_mul_of_left_mem_of_not_le _
      (preprojectiveMk_mem_preprojectiveGrade k Q (ofArrow_mem_grade_one b)) (by omega),
    smul_zero]

/-- Taking a positive-degree component commutes with a scalar multiple of an arrow multiple and a
subsequent right factor. -/
private theorem smul_ofArrow_mul_decompose_mul {i j : Symmetrify Q}
    (c : k) (b : i ⟶ j) (y e : preprojectiveAlgebra k Q) (m : ℕ) :
    c •
        (preprojectiveMk k Q (ofArrow b) *
          ((DirectSum.decompose (preprojectiveGrade k Q) y m : preprojectiveAlgebra k Q) * e)) =
      (DirectSum.decompose (preprojectiveGrade k Q)
          (c • (preprojectiveMk k Q (ofArrow b) * y)) (m + 1) :
        preprojectiveAlgebra k Q) * e := by
  rw [← mul_assoc, preprojectiveMk_ofArrow_mul_decompose, DirectSum.decompose_smul,
    DirectSum.smul_apply, Submodule.coe_smul, smul_mul_assoc]

/-- Cutting the degree-`m` component of an element of `e_v Π` down on the right by `e_i` gives an
element of `e_v Π_m e_i`. -/
private theorem decompose_mul_mem_preprojectiveCorner {v : Q} {y : preprojectiveAlgebra k Q}
    (hy : preprojectiveMk k Q (doubledVertexIdempotent k v) * y = y) (m : ℕ) (i : Symmetrify Q) :
    (DirectSum.decompose (preprojectiveGrade k Q) y m : preprojectiveAlgebra k Q) *
        preprojectiveMk k Q (vertexIdempotent k i) ∈
      preprojectiveCorner k Q m i (Symmetrify.of.obj v) := by
  have h0 : ∀ u : Symmetrify Q, preprojectiveMk k Q (vertexIdempotent k u) ∈
      preprojectiveGrade k Q 0 := fun u =>
    preprojectiveMk_mem_preprojectiveGrade k Q (vertexIdempotent_mem_grade_zero _)
  rw [doubledVertexIdempotent_def] at hy
  have hv : preprojectiveMk k Q (vertexIdempotent k (Symmetrify.of.obj v)) *
      (DirectSum.decompose (preprojectiveGrade k Q) y m : preprojectiveAlgebra k Q) =
        DirectSum.decompose (preprojectiveGrade k Q) y m := by
    conv_rhs => rw [← hy]
    rw [DirectSum.coe_decompose_mul_of_left_mem_of_le _ (h0 _) (Nat.zero_le m), Nat.sub_zero]
  refine mem_preprojectiveCorner_iff.2 ⟨?_, ?_⟩
  · simpa using mul_mem_preprojectiveGrade k Q (Submodule.coe_mem _) (h0 i)
  · rw [← mul_assoc, hv, mul_assoc, preprojectiveMk_vertexIdempotent_mul_self]

variable {k}

/-- The middle map `(z_b) ↦ ∑_b b z_b` of the Koszul complex of `S_v`, in degree `n + 1` and cut
down on the right by `e_i`. -/
private noncomputable def koszulSum (n : ℕ) (i : Symmetrify Q) (v : Q) :
    ((w : Symmetrify Q) → (w ⟶ Symmetrify.of.obj v) → preprojectiveCorner k Q n i w) →ₗ[k]
      preprojectiveAlgebra k Q :=
  ∑ w : Symmetrify Q, ∑ b : w ⟶ Symmetrify.of.obj v,
    (LinearMap.mulLeft k (preprojectiveMk k Q (ofArrow b))).comp
      ((preprojectiveCorner k Q n i w).subtype.comp
        ((LinearMap.proj (R := k)
            (φ := fun _ : w ⟶ Symmetrify.of.obj v => preprojectiveCorner k Q n i w) b).comp
          (LinearMap.proj (R := k) (φ := fun w : Symmetrify Q =>
            (w ⟶ Symmetrify.of.obj v) → preprojectiveCorner k Q n i w) w)))

private theorem koszulSum_apply (n : ℕ) (i : Symmetrify Q) (v : Q)
    (z : (w : Symmetrify Q) → (w ⟶ Symmetrify.of.obj v) → preprojectiveCorner k Q n i w) :
    koszulSum n i v z = ∑ w : Symmetrify Q, ∑ b : w ⟶ Symmetrify.of.obj v,
      preprojectiveMk k Q (ofArrow b) * (z w b : preprojectiveAlgebra k Q) := by
  simp [koszulSum, LinearMap.sum_apply]

/-- **Exactness of the Koszul complex at `e_v Π`, graded and cut down by `e_i`**: the middle map
has image `e_v Π_{n+1} e_i`. -/
private theorem range_koszulSum (n : ℕ) (i : Symmetrify Q) (v : Q) :
    LinearMap.range (koszulSum (k := k) n i v) =
      preprojectiveCorner k Q (n + 1) i (Symmetrify.of.obj v) := by
  refine le_antisymm ?_ fun x hx => ?_
  · rintro _ ⟨z, rfl⟩
    rw [koszulSum_apply]
    exact sum_mem fun w _ => sum_mem fun b _ =>
      preprojectiveMk_ofArrow_mul_mem_preprojectiveCorner b (z w b).2
  · obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.1 hx
    obtain ⟨hpn, hpc⟩ := mem_pathsBetween_iff.1 hp
    have hpv : vertexIdempotent k (Symmetrify.of.obj v) * p = p := by
      rw [← hpc, ← mul_assoc, ← mul_assoc, vertexIdempotent_mul_self]
    have hpi : p * vertexIdempotent k i = p := by
      rw [← hpc, mul_assoc, vertexIdempotent_mul_self]
    obtain ⟨z, hz, hpz⟩ := exists_eq_sum_ofArrow_mul (mem_pathsInto_iff.2 ⟨hpn, hpv⟩)
    refine ⟨fun w b => ⟨preprojectiveMk k Q (z w b * vertexIdempotent k i),
      mem_preprojectiveCorner_iff.2 ⟨?_, ?_⟩⟩, ?_⟩
    · obtain ⟨hzn, -⟩ := mem_pathsInto_iff.1 (hz w b)
      refine preprojectiveMk_mem_preprojectiveGrade k Q ?_
      simpa using SetLike.mul_mem_graded hzn (vertexIdempotent_mem_grade_zero (k := k) i)
    · obtain ⟨-, hzw⟩ := mem_pathsInto_iff.1 (hz w b)
      rw [← map_mul, ← map_mul, ← mul_assoc, hzw, mul_assoc, vertexIdempotent_mul_self]
    · rw [koszulSum_apply, AlgHom.toLinearMap_apply, ← hpi, hpz, Finset.sum_mul]
      simp only [map_sum, Finset.sum_mul, mul_assoc, map_mul]

/-- The hypothesis of `TauCeti.sum_preprojectiveMk_ofArrow_mul_eq_zero_iff` for a family of
corner elements. -/
private theorem forall_preprojectiveMk_vertexIdempotent_mul {n : ℕ} {i : Symmetrify Q} {v : Q}
    (z : (w : Symmetrify Q) → (w ⟶ Symmetrify.of.obj v) → preprojectiveCorner k Q n i w)
    (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v) :
    preprojectiveMk k Q (vertexIdempotent k w) * (z w b : preprojectiveAlgebra k Q) = z w b :=
  preprojectiveMk_vertexIdempotent_mul_of_mem_preprojectiveCorner (z w b).2

/-- In degree `1` the middle map of the Koszul complex is injective: a solution `z_b = ε_b b* y`
of `∑_b b z_b = 0` in degree `0` vanishes, since `b* y` has no component of degree `0`. -/
private theorem ker_koszulSum_zero (i : Symmetrify Q) (v : Q) :
    LinearMap.ker (koszulSum (k := k) 0 i v) = ⊥ := by
  refine (Submodule.eq_bot_iff _).2 fun z hz => ?_
  rw [LinearMap.mem_ker, koszulSum_apply] at hz
  obtain ⟨y, -, hy⟩ := (sum_preprojectiveMk_ofArrow_mul_eq_zero_iff k v
    (forall_preprojectiveMk_vertexIdempotent_mul z)).1 hz
  funext w b
  have h0 := (mem_preprojectiveCorner_iff.1 (z w b).2).1
  refine Subtype.ext ?_
  rw [Pi.zero_apply, Pi.zero_apply, Submodule.coe_zero, ← DirectSum.decompose_of_mem_same _ h0,
    hy w b, decompose_smul_ofArrow_mul_zero]

/-- The left map `y ↦ (ε_b b* y)_b` of the Koszul complex of `S_v`, in degree `m` and cut down on
the right by `e_i`. -/
private noncomputable def koszulDiff (m : ℕ) (i : Symmetrify Q) (v : Q) :
    preprojectiveCorner k Q m i (Symmetrify.of.obj v) →ₗ[k]
      ((w : Symmetrify Q) → (w ⟶ Symmetrify.of.obj v) → preprojectiveCorner k Q (m + 1) i w) :=
  LinearMap.pi fun _ => LinearMap.pi fun b =>
    LinearMap.codRestrict _
      (doubledArrowSign k b • (LinearMap.mulLeft k
        (preprojectiveMk k Q (ofArrow (Quiver.reverse b)))).comp
          (preprojectiveCorner k Q m i (Symmetrify.of.obj v)).subtype)
      fun y => Submodule.smul_mem _ _ (preprojectiveMk_ofArrow_mul_mem_preprojectiveCorner _ y.2)

private theorem koszulDiff_apply (m : ℕ) (i : Symmetrify Q) (v : Q)
    (y : preprojectiveCorner k Q m i (Symmetrify.of.obj v)) (w : Symmetrify Q)
    (b : w ⟶ Symmetrify.of.obj v) :
    (koszulDiff m i v y w b : preprojectiveAlgebra k Q) =
      doubledArrowSign k b • (preprojectiveMk k Q (ofArrow (Quiver.reverse b)) * y) :=
  rfl

/-- **Exactness of the Koszul complex at its middle term, graded and cut down by `e_i`.** -/
private theorem ker_koszulSum_succ (m : ℕ) (i : Symmetrify Q) (v : Q) :
    LinearMap.ker (koszulSum (k := k) (m + 1) i v) = LinearMap.range (koszulDiff m i v) := by
  refine le_antisymm (fun z hz => ?_) ?_
  · rw [LinearMap.mem_ker, koszulSum_apply] at hz
    obtain ⟨y, hyv, hy⟩ := (sum_preprojectiveMk_ofArrow_mul_eq_zero_iff k v
      (forall_preprojectiveMk_vertexIdempotent_mul z)).1 hz
    refine ⟨⟨_, decompose_mul_mem_preprojectiveCorner k hyv m i⟩, funext fun w => funext fun b =>
      Subtype.ext ?_⟩
    have h1 := (mem_preprojectiveCorner_iff.1 (z w b).2).1
    rw [koszulDiff_apply, Submodule.coe_mk, smul_ofArrow_mul_decompose_mul, ← hy w b,
      DirectSum.decompose_of_mem_same _ h1,
      mul_preprojectiveMk_vertexIdempotent_of_mem_preprojectiveCorner (z w b).2]
  · rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, koszulSum_apply]
    simp only [koszulDiff_apply]
    exact sum_preprojectiveMk_ofArrow_mul_doubledArrowSign_smul_eq_zero k v y

/-- The kernel of the left map of the Koszul complex consists of the elements killed by every
reverse arrow, the signs `ε_b` being units. -/
private theorem mem_ker_koszulDiff_iff (m : ℕ) (i : Symmetrify Q) (v : Q)
    (y : preprojectiveCorner k Q m i (Symmetrify.of.obj v)) :
    y ∈ LinearMap.ker (koszulDiff m i v) ↔ ∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
      preprojectiveMk k Q (ofArrow (Quiver.reverse b)) * y = 0 := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h w b
    have h' : (koszulDiff m i v y w b : preprojectiveAlgebra k Q) = 0 := by
      rw [h, Pi.zero_apply, Pi.zero_apply, Submodule.coe_zero]
    rw [koszulDiff_apply] at h'
    exact (smul_eq_zero.1 h').resolve_left (doubledArrowSign_ne_zero k b)
  · intro h
    funext w b
    exact Subtype.ext (by rw [koszulDiff_apply, h w b, smul_zero, Pi.zero_apply, Pi.zero_apply,
      Submodule.coe_zero])

/-- The domain of the middle map has dimension `∑_w #(w ⟶ v) dim e_w Π_n e_i`. -/
private theorem finrank_koszulSum_domain (n : ℕ) (i : Symmetrify Q) (v : Q) :
    Module.finrank k
        ((w : Symmetrify Q) → (w ⟶ Symmetrify.of.obj v) → preprojectiveCorner k Q n i w) =
      ∑ w : Symmetrify Q, Fintype.card (w ⟶ Symmetrify.of.obj v) *
        Module.finrank k (preprojectiveCorner k Q n i w) := by
  simp [Module.finrank_pi_fintype]

variable (k Q)

/-- **The graded corners in degree `0`**: `e_j Π_0 e_i` is the line spanned by `e_i` when `i = j`,
and is zero otherwise. -/
theorem finrank_preprojectiveCorner_zero [DecidableEq Q] (i j : Symmetrify Q) :
    Module.finrank k (preprojectiveCorner k Q 0 i j) = if i = j then 1 else 0 := by
  have hle : Module.finrank k (preprojectiveCorner k Q 0 i j) ≤
      Nat.card (PathBetween (Symmetrify Q) 0 i j) :=
    (Submodule.finrank_map_le _ _).trans (finrank_pathsBetween k 0 i j).le
  split_ifs with h
  · subst h
    have hcard : Nat.card (PathBetween (Symmetrify Q) 0 i i) = 1 := by
      refine Nat.card_eq_one_iff_exists.2 ⟨⟨Path.nil, rfl⟩, fun p => Subtype.ext ?_⟩
      exact Path.eq_nil_of_length_zero p.1 p.2
    refine le_antisymm (hcard ▸ hle)
      (Submodule.one_le_finrank_iff.2 ((Submodule.ne_bot_iff _).2 ?_))
    refine ⟨preprojectiveMk k Q (vertexIdempotent k i), mem_preprojectiveCorner_iff.2 ⟨
      preprojectiveMk_mem_preprojectiveGrade k Q (vertexIdempotent_mem_grade_zero i), ?_⟩,
      preprojectiveMk_vertexIdempotent_ne_zero k i⟩
    rw [preprojectiveMk_vertexIdempotent_mul_self, preprojectiveMk_vertexIdempotent_mul_self]
  · have hcard : Nat.card (PathBetween (Symmetrify Q) 0 i j) = 0 :=
      Nat.card_eq_zero.2 (Or.inl ⟨fun p => h (Path.eq_of_length_zero p.1 p.2)⟩)
    omega

/-- **The graded corners in degree `1`**: `e_j Π_1 e_i` has the arrows `i ⟶ j` of the doubled
quiver as a basis. -/
theorem finrank_preprojectiveCorner_one (i j : Symmetrify Q) :
    Module.finrank k (preprojectiveCorner k Q 1 i j) = Fintype.card (i ⟶ j) := by
  classical
  -- The Koszul complex is indexed by the vertices of `Q`.
  obtain ⟨v, rfl⟩ : ∃ v : Q, Symmetrify.of.obj v = j := ⟨j, rfl⟩
  have h := LinearMap.finrank_range_add_finrank_ker (koszulSum (k := k) 0 i v)
  rw [range_koszulSum, ker_koszulSum_zero, finrank_bot, add_zero, finrank_koszulSum_domain] at h
  rw [h, Finset.sum_eq_single i]
  · simp [finrank_preprojectiveCorner_zero]
  · intro w _ hw
    simp [finrank_preprojectiveCorner_zero, Ne.symm hw]
  · simp

/-- **The Koszul defect formula.** For vertices `i` and `v` and every degree `m`,

```text
dim e_v Π_{m+2} e_i + dim e_v Π_m e_i = ∑_w #(w ⟶ v) dim e_w Π_{m+1} e_i + dim K_m(i, v),
```

the sum running over the arrows of the doubled quiver into `v`, where `K_m(i, v)` is the space of
`y ∈ e_v Π_m e_i` killed by the reverse `b*` of every arrow `b` into `v`, the kernel of the left
map of the Koszul complex of `S_v`. -/
theorem finrank_preprojectiveCorner_add_two_add_finrank_preprojectiveCorner (m : ℕ)
    (i : Symmetrify Q) (v : Q) :
    Module.finrank k (preprojectiveCorner k Q (m + 2) i (Symmetrify.of.obj v)) +
        Module.finrank k (preprojectiveCorner k Q m i (Symmetrify.of.obj v)) =
      ∑ w : Symmetrify Q, Fintype.card (w ⟶ Symmetrify.of.obj v) *
          Module.finrank k (preprojectiveCorner k Q (m + 1) i w) +
        Module.finrank k ↥(preprojectiveCorner k Q m i (Symmetrify.of.obj v) ⊓
          ⨅ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
            LinearMap.ker
              (LinearMap.mulLeft k (preprojectiveMk k Q (ofArrow (Quiver.reverse b))))) := by
  have hΦ := LinearMap.finrank_range_add_finrank_ker (koszulSum (k := k) (m + 1) i v)
  rw [range_koszulSum, ker_koszulSum_succ, finrank_koszulSum_domain] at hΦ
  have hΨ := LinearMap.finrank_range_add_finrank_ker (koszulDiff (k := k) m i v)
  have hK : (LinearMap.ker (koszulDiff (k := k) m i v)).map
      (preprojectiveCorner k Q m i (Symmetrify.of.obj v)).subtype =
        preprojectiveCorner k Q m i (Symmetrify.of.obj v) ⊓
          ⨅ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
            LinearMap.ker
              (LinearMap.mulLeft k (preprojectiveMk k Q (ofArrow (Quiver.reverse b)))) := by
    ext x
    simp only [Submodule.mem_map, Submodule.mem_inf, Submodule.mem_iInf, Submodule.subtype_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, fun w b => LinearMap.mem_ker.2 ((mem_ker_koszulDiff_iff m i v y).1 hy w b)⟩
    · rintro ⟨hx, hy⟩
      exact ⟨⟨x, hx⟩, (mem_ker_koszulDiff_iff m i v _).2 fun w b => LinearMap.mem_ker.1 (hy w b),
        rfl⟩
  rw [← hK, Submodule.finrank_map_subtype_eq]
  -- `simp` cannot reach the degree `m + 1 + 1`, which sits inside the type of a `finrank`.
  rw [Nat.add_assoc, one_add_one_eq_two] at hΦ
  omega

/-- **The dimension recursion in degree `m + 2` is Koszul exactness in degree `m`.** The equality
`∑_w #(w ⟶ v) dim e_w Π_{m+1} e_i = dim e_v Π_{m+2} e_i + dim e_v Π_m e_i` holds exactly when no
nonzero `y ∈ e_v Π_m e_i` is killed by the reverse `b*` of every arrow `b` of the doubled quiver
into `v`. -/
theorem sum_card_mul_finrank_preprojectiveCorner_eq_iff (m : ℕ) (i : Symmetrify Q) (v : Q) :
    ∑ w : Symmetrify Q, Fintype.card (w ⟶ Symmetrify.of.obj v) *
          Module.finrank k (preprojectiveCorner k Q (m + 1) i w) =
        Module.finrank k (preprojectiveCorner k Q (m + 2) i (Symmetrify.of.obj v)) +
          Module.finrank k (preprojectiveCorner k Q m i (Symmetrify.of.obj v)) ↔
      ∀ y ∈ preprojectiveCorner k Q m i (Symmetrify.of.obj v),
        (∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
          preprojectiveMk k Q (ofArrow (Quiver.reverse b)) * y = 0) → y = 0 := by
  rw [finrank_preprojectiveCorner_add_two_add_finrank_preprojectiveCorner, left_eq_add,
    Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
  simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.mulLeft_apply,
    and_imp]

/-- **The matrix Hilbert series of the preprojective algebra**: its entry in row `j` and column `i`
is `∑_n dim (e_j Π_n e_i) Xⁿ`, the Hilbert series of the paths from `i` to `j`. -/
noncomputable def preprojectiveHilbertSeries : Matrix Q Q (PowerSeries ℤ) :=
  Matrix.of fun j i => PowerSeries.mk fun n =>
    (Module.finrank k (preprojectiveCorner k Q n (Symmetrify.of.obj i) (Symmetrify.of.obj j)) : ℤ)

/-- The coefficient of `Xⁿ` in the entry of the Hilbert series in row `j` and column `i` is
`dim (e_j Π_n e_i)`. -/
@[simp]
theorem coeff_preprojectiveHilbertSeries (n : ℕ) (i j : Q) :
    PowerSeries.coeff n (preprojectiveHilbertSeries k Q j i) =
      Module.finrank k (preprojectiveCorner k Q n (Symmetrify.of.obj i) (Symmetrify.of.obj j)) := by
  rw [preprojectiveHilbertSeries, Matrix.of_apply, PowerSeries.coeff_mk]

section HilbertSeries

open PowerSeries

variable [DecidableEq Q]

/-- The matrix `(1 + X²) I - X A`, for `A` the arrow-count matrix of the doubled quiver. -/
private noncomputable abbrev hilbertDenominator : Matrix Q Q ℤ⟦X⟧ :=
  ((1 : ℤ⟦X⟧) + X ^ 2) • (1 : Matrix Q Q ℤ⟦X⟧) -
    (X : ℤ⟦X⟧) • Matrix.of fun v w : Q =>
      (Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) : ℤ⟦X⟧)

/-- The entries of `((1 + X²) I - X A) H`, for `A` the arrow-count matrix of the doubled quiver. -/
private theorem mul_preprojectiveHilbertSeries_apply (v i : Q) :
    (hilbertDenominator Q * preprojectiveHilbertSeries k Q) v i =
      ((1 : ℤ⟦X⟧) + X ^ 2) * preprojectiveHilbertSeries k Q v i -
        (X : ℤ⟦X⟧) * ∑ w : Q, (Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) : ℤ⟦X⟧) *
          preprojectiveHilbertSeries k Q w i := by
  rw [sub_mul]
  simp only [Matrix.smul_mul, Matrix.one_mul, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.of_apply]

/-- The coefficient of `X^{m+2}` in an entry of `((1 + X²) I - X A) H`. -/
private theorem coeff_add_two_mul_preprojectiveHilbertSeries (m : ℕ) (v i : Q) :
    coeff (m + 2) ((hilbertDenominator Q * preprojectiveHilbertSeries k Q) v i) =
      ((Module.finrank k (preprojectiveCorner k Q (m + 2) (Symmetrify.of.obj i)
          (Symmetrify.of.obj v)) +
        Module.finrank k (preprojectiveCorner k Q m (Symmetrify.of.obj i) (Symmetrify.of.obj v)) :
          ℕ) : ℤ) -
        ((∑ w : Q, Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) *
          Module.finrank k (preprojectiveCorner k Q (m + 1) (Symmetrify.of.obj i)
            (Symmetrify.of.obj w)) : ℕ) : ℤ) := by
  simp only [mul_preprojectiveHilbertSeries_apply, map_sub, add_mul, one_mul, map_add,
    coeff_X_pow_mul', ite_eq_left (by omega : 2 ≤ m + 2), Nat.add_sub_cancel,
    coeff_succ_X_mul, map_sum, coeff_natCast_mul, coeff_preprojectiveHilbertSeries, Nat.cast_add,
    Nat.cast_sum, Nat.cast_mul]

/-- The constant coefficient of the Hilbert-series product is the identity matrix. -/
private theorem coeff_zero_mul_preprojectiveHilbertSeries (v i : Q) :
    coeff 0 ((hilbertDenominator Q * preprojectiveHilbertSeries k Q) v i) =
      if v = i then 1 else 0 := by
  rw [mul_preprojectiveHilbertSeries_apply]
  simp only [map_sub, coeff_zero_X_mul, sub_zero, add_mul, one_mul, map_add,
    coeff_X_pow_mul', ite_eq_right (by omega : ¬2 ≤ 0), add_zero]
  rw [coeff_preprojectiveHilbertSeries, finrank_preprojectiveCorner_zero]
  by_cases hvi : v = i
  · subst i
    rw [ite_eq_left rfl, ite_eq_left rfl]
    norm_num
  · rw [ite_eq_right fun e => hvi e.symm, ite_eq_right hvi]
    simp

/-- The linear coefficient of the Hilbert-series product vanishes. -/
private theorem coeff_one_mul_preprojectiveHilbertSeries (v i : Q) :
    coeff 1 ((hilbertDenominator Q * preprojectiveHilbertSeries k Q) v i) = 0 := by
  rw [mul_preprojectiveHilbertSeries_apply]
  simp only [map_sub, add_mul, one_mul, map_add, coeff_X_pow_mul',
    ite_eq_right (by omega : ¬2 ≤ 1), add_zero, coeff_preprojectiveHilbertSeries,
    finrank_preprojectiveCorner_one, coeff_succ_X_mul, map_sum]
  rw [Finset.sum_eq_single i]
  · rw [coeff_natCast_mul, coeff_preprojectiveHilbertSeries,
      finrank_preprojectiveCorner_zero, ite_eq_left rfl]
    simp
  · intro w _ hw
    rw [coeff_natCast_mul, coeff_preprojectiveHilbertSeries,
      finrank_preprojectiveCorner_zero, ite_eq_right fun e => hw e.symm, Nat.cast_zero, mul_zero]
  · simp

/-- **The Hilbert series identity characterizes injectivity of the left Koszul map.** Let `A` be
the arrow-count matrix of the doubled quiver, `A_{v,w} = #(w ⟶ v)`, and `H` the matrix Hilbert
series of `Π`. Then

```text
((1 + X²) I - X A) H = I
```

holds exactly when, at every vertex `v`, the only `y ∈ e_v Π` killed by the reverse `b*` of every
arrow `b` of the doubled quiver into `v` is `0`: that is, exactly when the left-hand map of the
Koszul complex of every vertex module is injective, so that these complexes are projective
resolutions. -/
theorem mul_preprojectiveHilbertSeries_eq_one_iff :
    (((1 : ℤ⟦X⟧) + X ^ 2) • (1 : Matrix Q Q ℤ⟦X⟧) -
        (X : ℤ⟦X⟧) • Matrix.of fun v w : Q =>
          (Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) : ℤ⟦X⟧)) *
        preprojectiveHilbertSeries k Q = 1 ↔
      ∀ (v : Q) (y : preprojectiveAlgebra k Q),
        preprojectiveMk k Q (doubledVertexIdempotent k v) * y = y →
          (∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
            preprojectiveMk k Q (ofArrow (Quiver.reverse b)) * y = 0) → y = 0 := by
  classical
  -- In degree `m + 2` the identity is the dimension recursion, that is, Koszul exactness.
  have hdeg : ∀ (m : ℕ) (v i : Q),
      coeff (m + 2) ((hilbertDenominator Q * preprojectiveHilbertSeries k Q) v i) =
          coeff (m + 2) ((1 : Matrix Q Q ℤ⟦X⟧) v i) ↔
        ∀ y ∈ preprojectiveCorner k Q m (Symmetrify.of.obj i) (Symmetrify.of.obj v),
          (∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
            preprojectiveMk k Q (ofArrow (Quiver.reverse b)) * y = 0) → y = 0 := by
    intro m v i
    -- The vertices of the doubled quiver are those of `Q`.
    rw [coeff_add_two_mul_preprojectiveHilbertSeries,
      Fintype.sum_equiv (Equiv.ofBijective _ symmetrify_of_obj_bijective)
        (fun w : Q => Fintype.card (Symmetrify.of.obj w ⟶ Symmetrify.of.obj v) *
          Module.finrank k (preprojectiveCorner k Q (m + 1) (Symmetrify.of.obj i)
            (Symmetrify.of.obj w)))
        (fun w : Symmetrify Q => Fintype.card (w ⟶ Symmetrify.of.obj v) *
          Module.finrank k (preprojectiveCorner k Q (m + 1) (Symmetrify.of.obj i) w)) fun _ => rfl,
      ← sum_card_mul_finrank_preprojectiveCorner_eq_iff, Matrix.one_apply]
    have h0 : coeff (m + 2) (if v = i then (1 : ℤ⟦X⟧) else 0) = 0 := by
      split_ifs <;> simp [coeff_one]
    rw [h0, sub_eq_zero, Nat.cast_inj, eq_comm]
  constructor
  · intro h v y hy hb
    have hm : ∀ (m : ℕ) (u : Symmetrify Q),
        (DirectSum.decompose (preprojectiveGrade k Q) y m : preprojectiveAlgebra k Q) *
          preprojectiveMk k Q (vertexIdempotent k u) = 0 := by
      intro m u
      refine (hdeg m v u).1 (congrArg (fun M => coeff (m + 2) (M v u)) h) _
        (decompose_mul_mem_preprojectiveCorner k hy m u) fun w b => ?_
      rw [← mul_assoc, preprojectiveMk_ofArrow_mul_decompose, hb w b, DirectSum.decompose_zero,
        DirectSum.zero_apply, ZeroMemClass.coe_zero, zero_mul]
    rw [← DirectSum.sum_support_decompose (preprojectiveGrade k Q) y]
    refine Finset.sum_eq_zero fun m _ => ?_
    rw [← mul_one (DirectSum.decompose (preprojectiveGrade k Q) y m : preprojectiveAlgebra k Q),
      ← map_one (preprojectiveMk k Q), one_def, map_sum, Finset.mul_sum]
    exact Finset.sum_eq_zero fun u _ => hm m u
  · intro h
    refine Matrix.ext fun v i => PowerSeries.ext fun n => ?_
    obtain _ | _ | m := n
    · rw [coeff_zero_mul_preprojectiveHilbertSeries, Matrix.one_apply]
      by_cases hvi : v = i
      · rw [ite_eq_left hvi, ite_eq_left hvi, coeff_one, ite_eq_left rfl]
      · rw [ite_eq_right hvi, ite_eq_right hvi, map_zero]
    · rw [coeff_one_mul_preprojectiveHilbertSeries, Matrix.one_apply]
      by_cases hvi : v = i
      · rw [ite_eq_left hvi, coeff_one, ite_eq_right (by omega : 1 ≠ 0)]
      · rw [ite_eq_right hvi, map_zero]
    · exact (hdeg m v i).2 fun y hy => h v y (by
        rw [doubledVertexIdempotent_def]
        exact preprojectiveMk_vertexIdempotent_mul_of_mem_preprojectiveCorner hy)

end HilbertSeries

end Field

end TauCeti
