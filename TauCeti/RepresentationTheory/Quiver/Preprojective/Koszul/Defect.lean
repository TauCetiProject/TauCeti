/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Injective.SelfInjective
public import TauCeti.RepresentationTheory.Quiver.Preprojective.HilbertSeries.Basic
public import TauCeti.RepresentationTheory.Quiver.Preprojective.Resolution
public import TauCeti.RepresentationTheory.Quiver.Preprojective.SelfInjective

/-!
# The Koszul defect of a finite-dimensional preprojective algebra

Let `Q` be a finite quiver and `Π = Π_k(Q)` its preprojective algebra over a field `k`. The Koszul
complex of the vertex module `S_v`,

```text
0 ⟶ e_v Π ⟶ ⨁_{b : i ⟶ v} e_i Π ⟶ e_v Π ⟶ S_v ⟶ 0,
```

is exact except possibly at its left end, whose defect is the kernel

```text
K_v = {y ∈ e_v Π | b* y = 0 for every arrow b of the doubled quiver into v}
```

of the left map `y ↦ (ε_b b* y)_b` (`TauCeti.preprojectiveKoszulLeft`). Since the reverses `b*` are
all the arrows leaving `v`, `K_v` consists of the elements of `e_v Π` killed by every path of
positive length on the left. It vanishes at every vertex exactly when these Koszul complexes are
projective resolutions, as for every orientation of a connected graph which is not a tree
(`TauCeti.preprojectiveKoszulLeft_injective_of_not_isAcyclic`). This file computes it when `Π` is
finite-dimensional, which by
`TauCeti.finiteDimensional_preprojectiveAlgebra_of_isSimplyLaced` covers every orientation of a
simply-laced Dynkin diagram: **`K_v` is one-dimensional at every vertex**, spanned by a single
element `y_v` of some graded corner `e_v Π_n e_u`. So the Koszul complex fails to be a resolution
by exactly a one-dimensional simple module at its left end, concentrated in one degree.

The proof uses only that `Π` is self-injective on both sides
(`TauCeti.moduleInjective_preprojectiveAlgebra_of_finiteDimensional` and its right-handed
companion), through the annihilator criterion of Ikeda and Nakayama
(`TauCeti.exists_eq_sum_mul_of_forall_mul_eq_zero`).

* `K_v` is nonzero. Otherwise the elements killed on the left by every arrow `b*` leaving `v`
  would all be killed by `e_v`, and right self-injectivity would write `e_v` as a combination
  `∑ c_b b*` of those arrows, which has no component in degree zero.
* Every `r ∈ Π` acts on all of `K_v` by one scalar, the coefficient of `e_v` in `r`, since paths
  of positive length kill `K_v`. So for `y` and `z` in `K_v`, with `y ≠ 0`, the left annihilator
  of `y` is contained in that of `z`, and left self-injectivity gives `z ∈ y Π`.
* For a nonzero homogeneous `y ∈ K_v` of largest degree, cut down to a single vertex on the right,
  every arrow kills `y` on the right too, so `y Π` is the line `k y`.

Through the Koszul defect formula
(`TauCeti.finrank_preprojectiveCorner_add_two_add_finrank_preprojectiveCorner`), the dimensions of
the graded corners `e_v Π_n e_i` of a finite-dimensional preprojective algebra therefore satisfy
the recursion `dim e_v Π_{m+2} e_i + dim e_v Π_m e_i = ∑_w #(w ⟶ v) dim e_w Π_{m+1} e_i` of a
Koszul algebra in every degree `m` and at every vertex `i`, except at the single pair `(n, u)`
attached to `v`, where the left side exceeds the right by one. Brenner, Butler and King's almost
Koszul property of the Dynkin preprojective algebras asks moreover that every `K_v` sit in the top
degree of `Π`; that identification of the degree `n` is not proved here.

## Main results

* `TauCeti.exists_mem_preprojectiveCorner_forall_exists_eq_smul`: `K_v` is the line through a
  nonzero element of a graded corner `e_v Π_n e_u`.
* `TauCeti.finrank_ker_preprojectiveKoszulLeft`: the kernel of the left Koszul map is
  one-dimensional.
* `TauCeti.exists_forall_finrank_preprojectiveCorner_inf_iInf_ker_eq`: its graded pieces
  `K_m(i, v) ⊆ e_v Π_m e_i` all vanish except one, which is one-dimensional.
* `TauCeti.exists_forall_finrank_preprojectiveCorner_add_two_add_finrank_preprojectiveCorner`:
  the dimension recursion with its single defect.

## References

* S. Brenner, M. C. R. Butler and A. D. King, *Periodic algebras which are almost Koszul*,
  Algebr. Represent. Theory 5 (2002), Sections 3 and 4.
* P. Etingof and C.-H. Eu, *Koszulity and the Hilbert series of preprojective algebras*, Math.
  Res. Lett. 14 (2007), Sections 2 and 3.
* M. Ikeda and T. Nakayama, *On some characteristic properties of quasi-Frobenius and regular
  rings*, Proc. Amer. Math. Soc. 5 (1954).
-/

public section

namespace TauCeti

open _root_.Quiver PathAlgebra

universe u v w

variable (k : Type w) {Q : Type u} [Field k] [Quiver.{v} Q] [Fintype Q]
  [∀ i j : Q, Fintype (i ⟶ j)]

local notation "Π" => preprojectiveAlgebra k Q
local notation "π" => preprojectiveMk k Q

attribute [local instance] preprojectiveGradedAlgebra

/-! ### Paths of positive length kill the left Koszul kernel -/

section Kernel

variable {k} {v : Q} {y : preprojectiveAlgebra k Q}

/-- Every arrow of the doubled quiver kills, on the left, an element of `e_v Π` killed by the
arrows leaving `v`. -/
private theorem preprojectiveMk_ofArrow_mul_eq_zero (hy : π (doubledVertexIdempotent k v) * y = y)
    (hb : ∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
      π (ofArrow (Quiver.reverse b)) * y = 0)
    {i j : Symmetrify Q} (c : i ⟶ j) : π (ofArrow c) * y = 0 := by
  by_cases hi : i = Symmetrify.of.obj v
  · subst i
    simpa only [Quiver.reverse_reverse] using hb j (Quiver.reverse c)
  · rw [← hy, ← mul_assoc, ← map_mul, doubledVertexIdempotent_def, ofArrow_eq_ofPath,
      ofPath_mul_vertexIdempotent_of_ne _ (Ne.symm hi), map_zero, zero_mul]

/-- Every path of positive length kills, on the left, an element of `e_v Π` killed by the arrows
leaving `v`. -/
private theorem preprojectiveMk_ofPath_mul_eq_zero (hy : π (doubledVertexIdempotent k v) * y = y)
    (hb : ∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
      π (ofArrow (Quiver.reverse b)) * y = 0)
    {i j : Symmetrify Q} (p : Path i j) (hp : 0 < p.length) : π (ofPath ⟨i, j, p⟩) * y = 0 := by
  induction p with
  | nil => exact absurd hp (lt_irrefl 0)
  | cons p' c ih =>
    rw [← ofArrow_mul_ofPath, map_mul, mul_assoc]
    rcases Nat.eq_zero_or_pos p'.length with h0 | hpos
    · obtain rfl := Path.eq_of_length_zero p' h0
      obtain rfl := Path.eq_nil_of_length_zero p' h0
      rw [← mul_assoc, ← map_mul, ← vertexIdempotent_eq_ofPath, ofArrow_eq_ofPath,
        ofPath_mul_vertexIdempotent, ← ofArrow_eq_ofPath]
      exact preprojectiveMk_ofArrow_mul_eq_zero hy hb c
    · rw [ih hpos, mul_zero]

variable (k) in
/-- **Every element acts on the left Koszul kernel by a scalar**: for `r ∈ Π` there is one `t ∈ k`
with `r y = t y` for every `y ∈ e_v Π` killed by the arrows leaving `v`, namely the coefficient of
the trivial path at `v` in `r`. -/
private theorem exists_forall_mul_eq_smul (v : Q) (r : Π) :
    ∃ t : k, ∀ y : Π, π (doubledVertexIdempotent k v) * y = y →
      (∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
        π (ofArrow (Quiver.reverse b)) * y = 0) → r * y = t • y := by
  obtain ⟨f, rfl⟩ := preprojectiveMk_surjective k Q r
  induction f using PathAlgebra.induction_linear with
  | zero => exact ⟨0, fun y _ _ => by rw [map_zero, zero_mul, zero_smul]⟩
  | add f f' hf hf' =>
    obtain ⟨t, ht⟩ := hf
    obtain ⟨t', ht'⟩ := hf'
    exact ⟨t + t', fun y hy hb => by rw [map_add, add_mul, ht y hy hb, ht' y hy hb, add_smul]⟩
  | single x c =>
    obtain ⟨i, j, p⟩ := x
    rw [single_eq_smul_ofPath, map_smul]
    rcases Nat.eq_zero_or_pos p.length with h0 | hpos
    · obtain rfl := Path.eq_of_length_zero p h0
      obtain rfl := Path.eq_nil_of_length_zero p h0
      by_cases hi : i = Symmetrify.of.obj v
      · subst i
        refine ⟨c, fun y hy _ => ?_⟩
        rw [smul_mul_assoc, ← vertexIdempotent_eq_ofPath, ← doubledVertexIdempotent_def, hy]
      · refine ⟨0, fun y hy _ => ?_⟩
        rw [zero_smul, smul_mul_assoc, ← hy, ← mul_assoc, ← map_mul, ← vertexIdempotent_eq_ofPath,
          doubledVertexIdempotent_def, vertexIdempotent_mul_vertexIdempotent_of_ne hi, map_zero,
          zero_mul, smul_zero]
    · exact ⟨0, fun y hy hb => by
        rw [smul_mul_assoc, preprojectiveMk_ofPath_mul_eq_zero hy hb p hpos, smul_zero,
          zero_smul]⟩

/-- **The left Koszul kernel is generated by any of its nonzero elements**, over a left
self-injective preprojective algebra: if `y` and `z` lie in `e_v Π` and are killed by the arrows
leaving `v`, and `y ≠ 0`, then `z ∈ y Π`. -/
private theorem exists_eq_mul_of_ne_zero [Module.Injective Π Π] {z : Π}
    (hy : π (doubledVertexIdempotent k v) * y = y)
    (hyb : ∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
      π (ofArrow (Quiver.reverse b)) * y = 0) (hy0 : y ≠ 0)
    (hz : π (doubledVertexIdempotent k v) * z = z)
    (hzb : ∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
      π (ofArrow (Quiver.reverse b)) * z = 0) :
    ∃ c : Π, z = y * c := by
  -- Every scalar killing `y` kills `z`, since `Π` acts on both by the same scalars and `y ≠ 0`.
  obtain ⟨c, hc⟩ := exists_eq_sum_mul_of_forall_mul_eq_zero (ι := Unit) (a := fun _ => y)
    (x := z) fun r hr => by
      obtain ⟨t, ht⟩ := exists_forall_mul_eq_smul k v r
      have h0 : t • y = 0 := by rw [← ht y hy hyb]; exact hr ()
      rw [ht z hz hzb, (smul_eq_zero.1 h0).resolve_right hy0, zero_smul]
  exact ⟨c (), by simpa using hc⟩

end Kernel

/-! ### The left Koszul kernel of a finite-dimensional preprojective algebra -/

section FiniteDimensional

/-- The left Koszul kernel of a finite-dimensional preprojective algebra is nonzero at every
vertex `v`: some nonzero `y ∈ e_v Π` is killed by the reverse `b*` of every arrow `b` of the doubled
quiver into `v`. -/
private theorem exists_ne_zero_forall_ofArrow_reverse_mul_eq_zero
    [FiniteDimensional k Π] (v : Q) :
    ∃ y : Π, π (doubledVertexIdempotent k v) * y = y ∧ y ≠ 0 ∧
      ∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
        π (ofArrow (Quiver.reverse b)) * y = 0 := by
  classical
  by_contra hK
  have := moduleInjective_op_preprojectiveAlgebra_of_finiteDimensional k (Q := Q)
  -- Every `r` killed on the left by the arrows leaving `v` is killed by `e_v`, since `e_v r` lies
  -- in the left Koszul kernel; so `e_v` lies in the left ideal generated by those arrows.
  obtain ⟨c, hc⟩ := exists_eq_sum_mul_of_forall_mul_eq_zero'
    (ι := Σ w : Symmetrify Q, w ⟶ Symmetrify.of.obj v)
    (a := fun b => π (ofArrow (Quiver.reverse b.2)))
    (x := π (doubledVertexIdempotent k v)) fun r hr => by
      by_contra hne
      refine hK ⟨π (doubledVertexIdempotent k v) * r, ?_, hne, fun w b => ?_⟩
      · rw [← mul_assoc, ← map_mul, doubledVertexIdempotent_def, vertexIdempotent_mul_self]
      · rw [← mul_assoc, ← map_mul, doubledVertexIdempotent_def, ofArrow_eq_ofPath,
          ofPath_mul_vertexIdempotent, ← ofArrow_eq_ofPath]
        exact hr ⟨w, b⟩
  -- That left ideal has no component in degree zero, while `e_v` lies in degree zero.
  have h0 := congrArg (GradedRing.proj (preprojectiveGrade k Q) 0) hc
  simp only [map_sum, GradedRing.proj_apply] at h0
  rw [doubledVertexIdempotent_def, DirectSum.decompose_of_mem_same _
      (preprojectiveMk_mem_preprojectiveGrade k Q (vertexIdempotent_mem_grade_zero _)),
    Finset.sum_eq_zero fun b _ => DirectSum.coe_decompose_mul_of_right_mem_of_not_le _
      (preprojectiveMk_mem_preprojectiveGrade k Q (ofArrow_mem_grade_one _)) (by omega)] at h0
  exact preprojectiveMk_vertexIdempotent_ne_zero k (Symmetrify.of.obj v) h0

/-- **The left Koszul kernel of a finite-dimensional preprojective algebra is a line.** At every
vertex `v` there are a degree `n`, a vertex `u` and a nonzero `y ∈ e_v Π_n e_u`, killed by the
reverse `b*` of every arrow `b` of the doubled quiver into `v`, such that every `z ∈ e_v Π` killed
by all those `b*` is a scalar multiple of `y`. -/
theorem exists_mem_preprojectiveCorner_forall_exists_eq_smul [FiniteDimensional k Π] (v : Q) :
    ∃ (n : ℕ) (u : Q) (y : Π),
      y ∈ preprojectiveCorner k Q n (Symmetrify.of.obj u) (Symmetrify.of.obj v) ∧ y ≠ 0 ∧
      (∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
        π (ofArrow (Quiver.reverse b)) * y = 0) ∧
      ∀ z : Π, π (doubledVertexIdempotent k v) * z = z →
        (∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
          π (ofArrow (Quiver.reverse b)) * z = 0) → ∃ t : k, z = t • y := by
  classical
  have := moduleInjective_preprojectiveAlgebra_of_finiteDimensional k (Q := Q)
  have h0 (i : Symmetrify Q) : π (vertexIdempotent k i) ∈ preprojectiveGrade k Q 0 :=
    preprojectiveMk_mem_preprojectiveGrade k Q (vertexIdempotent_mem_grade_zero i)
  -- The left Koszul kernel `K_v`, and its closure under right multiplication and under taking
  -- homogeneous components.
  let K : Π → Prop := fun y => π (doubledVertexIdempotent k v) * y = y ∧
    ∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v), π (ofArrow (Quiver.reverse b)) * y = 0
  have hmul {y : Π} (hy : K y) (r : Π) : K (y * r) :=
    ⟨by rw [← mul_assoc, hy.1], fun w b => by rw [← mul_assoc, hy.2 w b, zero_mul]⟩
  have hdec {y : Π} (hy : K y) (m : ℕ) :
      K (DirectSum.decompose (preprojectiveGrade k Q) y m : Π) := by
    refine ⟨?_, fun w b => ?_⟩
    · conv_rhs => rw [← hy.1]
      rw [doubledVertexIdempotent_def,
        DirectSum.coe_decompose_mul_of_left_mem_of_le _ (h0 _) (Nat.zero_le m), Nat.sub_zero]
    · rw [← Nat.add_sub_cancel m 1, ← DirectSum.coe_decompose_mul_of_left_mem_of_le _
        (preprojectiveMk_mem_preprojectiveGrade k Q (ofArrow_mem_grade_one _)) (by omega),
        hy.2 w b, DirectSum.decompose_zero, DirectSum.zero_apply, ZeroMemClass.coe_zero]
  -- Take a nonzero homogeneous `y₁ ∈ K_v` of the largest possible degree `n`.
  let L : Set ℕ := {m | ∃ y, K y ∧ y ∈ preprojectiveGrade k Q m ∧ y ≠ 0}
  have hL_fin : L.Finite := by
    refine (WellFoundedGT.finite_ne_bot_of_iSupIndep
      (isInternal_preprojectiveGrade k Q).submodule_iSupIndep).subset ?_
    rintro m ⟨y, -, hym, hy0⟩ hbot
    rw [hbot, Submodule.mem_bot] at hym
    exact hy0 hym
  have hL_ne : L.Nonempty := by
    obtain ⟨y₀, hy₀, hy₀0, hy₀b⟩ :=
      exists_ne_zero_forall_ofArrow_reverse_mul_eq_zero k v
    obtain ⟨m, hm⟩ : ∃ m, (DirectSum.decompose (preprojectiveGrade k Q) y₀ m : Π) ≠ 0 := by
      by_contra! h
      refine hy₀0 ?_
      rw [← DirectSum.sum_support_decompose (preprojectiveGrade k Q) y₀]
      exact Finset.sum_eq_zero fun m _ => h m
    exact ⟨m, _, hdec ⟨hy₀, hy₀b⟩ m, Submodule.coe_mem _, hm⟩
  obtain ⟨y₁, hy₁, hy₁n, hy₁0⟩ := Nat.sSup_mem hL_ne hL_fin.bddAbove
  -- By maximality of `n`, every arrow also kills `y₁` on the right.
  have hright {i j : Symmetrify Q} (c : i ⟶ j) : y₁ * π (ofArrow c) = 0 := by
    by_contra hc
    have hle := le_csSup hL_fin.bddAbove ⟨_, hmul hy₁ _, mul_mem_preprojectiveGrade k Q hy₁n
      (preprojectiveMk_mem_preprojectiveGrade k Q (ofArrow_mem_grade_one c)), hc⟩
    omega
  -- Cut `y₁` down on the right to a vertex `u` where it does not vanish.
  obtain ⟨u, -, hu⟩ : ∃ u ∈ Finset.univ, y₁ * π (vertexIdempotent k u) ≠ 0 := by
    by_contra! h
    refine hy₁0 ?_
    rw [← mul_one y₁, ← map_one π, one_def, map_sum, Finset.mul_sum]
    exact Finset.sum_eq_zero h
  set y := y₁ * π (vertexIdempotent k u) with hy_def
  have hy : K y := hmul hy₁ _
  -- Right multiplication by `Π` acts on the line `k y` through the coefficient of `e_u`.
  have hline (r : Π) : ∃ t : k, y * r = t • y := by
    obtain ⟨f, rfl⟩ := preprojectiveMk_surjective k Q r
    induction f using PathAlgebra.induction_linear with
    | zero => exact ⟨0, by rw [map_zero, mul_zero, zero_smul]⟩
    | add f f' hf hf' =>
      obtain ⟨t, ht⟩ := hf
      obtain ⟨t', ht'⟩ := hf'
      exact ⟨t + t', by rw [map_add, mul_add, ht, ht', add_smul]⟩
    | single x c =>
      obtain ⟨i, j, p⟩ := x
      rw [single_eq_smul_ofPath, map_smul, mul_smul_comm]
      cases p with
      | nil =>
        rw [← vertexIdempotent_eq_ofPath, hy_def, mul_assoc, ← map_mul]
        by_cases hi : u = i
        · subst hi
          exact ⟨c, by rw [vertexIdempotent_mul_self]⟩
        · exact ⟨0, by rw [vertexIdempotent_mul_vertexIdempotent_of_ne hi, map_zero, mul_zero,
            smul_zero, zero_smul]⟩
      | cons p' c' =>
        refine ⟨0, ?_⟩
        rw [← ofArrow_mul_ofPath, map_mul, hy_def, ← mul_assoc, mul_assoc y₁, ← map_mul,
          vertexIdempotent_mul_ofArrow]
        split_ifs
        · rw [hright, zero_mul, smul_zero, zero_smul]
        · rw [map_zero, mul_zero, zero_mul, smul_zero, zero_smul]
  obtain ⟨u, rfl⟩ : ∃ u' : Q, Symmetrify.of.obj u' = u := ⟨u, rfl⟩
  refine ⟨sSup L, u, y, mem_preprojectiveCorner_iff.2 ⟨?_, ?_⟩, hu, hy.2, fun z hz hzb => ?_⟩
  · simpa only [add_zero] using mul_mem_preprojectiveGrade k Q hy₁n (h0 _)
  · rw [← doubledVertexIdempotent_def, hy.1, hy_def, mul_assoc, ← map_mul,
      vertexIdempotent_mul_self]
  · obtain ⟨r, rfl⟩ := exists_eq_mul_of_ne_zero hy.1 hy.2 hu hz hzb
    exact hline r

/-- **The kernel of the left Koszul map of a finite-dimensional preprojective algebra is
one-dimensional**, at every vertex: the Koszul complex of the vertex module `S_v` fails to be a
resolution by exactly a line at its left end. -/
theorem finrank_ker_preprojectiveKoszulLeft [FiniteDimensional k Π] (v : Q) :
    Module.finrank k (LinearMap.ker (preprojectiveKoszulLeft k v)) = 1 := by
  obtain ⟨n, u, y, hy, hy0, hyb, hz⟩ := exists_mem_preprojectiveCorner_forall_exists_eq_smul k v
  have hyv : π (vertexIdempotent k (Symmetrify.of.obj v)) * y = y :=
    preprojectiveMk_vertexIdempotent_mul_of_mem_preprojectiveCorner hy
  -- Membership in the kernel: the signs `ε_b = ±1` do not matter.
  have hmem (x : preprojectiveRightProjective k (Symmetrify.of.obj v)) :
      x ∈ LinearMap.ker (preprojectiveKoszulLeft k v) ↔
        ∀ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
          π (ofArrow (Quiver.reverse b)) * x = 0 := by
    rw [LinearMap.mem_ker]
    constructor
    · intro h w b
      have h' := congrArg (fun z => doubledArrowSign k b • (z w b : Π)) h
      simpa only [coe_preprojectiveKoszulLeft_apply, smul_smul, doubledArrowSign_mul_self,
        one_smul, Pi.zero_apply, ZeroMemClass.coe_zero, smul_zero] using h'
    · intro h
      ext w b
      rw [coe_preprojectiveKoszulLeft_apply, h w b, smul_zero]
      rfl
  -- The kernel is the line through `y`: `t ↦ t • y` is a bijection from `k`.
  let y' : LinearMap.ker (preprojectiveKoszulLeft k v) :=
    ⟨⟨y, (mem_preprojectiveRightProjective_iff k _ y).2 hyv⟩, (hmem _).2 hyb⟩
  have hbij : Function.Bijective (LinearMap.toSpanSingleton k _ y') := by
    refine ⟨fun s t hst => ?_, fun x => ?_⟩
    · have h := congrArg (fun x : LinearMap.ker (preprojectiveKoszulLeft k v) =>
        ((x : preprojectiveRightProjective k (Symmetrify.of.obj v)) : Π)) hst
      simp only [LinearMap.toSpanSingleton_apply, Submodule.coe_smul_of_tower, y'] at h
      exact smul_left_injective k hy0 h
    · obtain ⟨t, ht⟩ := hz x (by
        rw [doubledVertexIdempotent_def]
        exact (mem_preprojectiveRightProjective_iff k _ _).1 x.1.2) ((hmem _).1 x.2)
      exact ⟨t, by ext; simp [y', ht]⟩
  rw [← (LinearEquiv.ofBijective _ hbij).finrank_eq, Module.finrank_self]

/-- **The graded pieces of the left Koszul kernel**: for a finite-dimensional preprojective
algebra and a vertex `v`, the spaces `K_m(i, v)` of `y ∈ e_v Π_m e_i` killed by the reverse `b*` of
every arrow `b` of the doubled quiver into `v` all vanish, except for a single pair `(n, u)`, where
`K_n(u, v)` is one-dimensional. -/
theorem exists_forall_finrank_preprojectiveCorner_inf_iInf_ker_eq [DecidableEq Q]
    [FiniteDimensional k Π] (v : Q) :
    ∃ (n : ℕ) (u : Q), ∀ (m : ℕ) (i : Q),
      Module.finrank k ↥(preprojectiveCorner k Q m (Symmetrify.of.obj i) (Symmetrify.of.obj v) ⊓
        ⨅ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
          LinearMap.ker (LinearMap.mulLeft k (π (ofArrow (Quiver.reverse b))))) =
        if m = n ∧ i = u then 1 else 0 := by
  obtain ⟨n, u, y, hy, hy0, hyb, hz⟩ := exists_mem_preprojectiveCorner_forall_exists_eq_smul k v
  refine ⟨n, u, fun m i => ?_⟩
  -- Every element of `K_m(i, v)` is a multiple of `y`.
  have hK {x : Π} (hx : x ∈ preprojectiveCorner k Q m (Symmetrify.of.obj i) (Symmetrify.of.obj v) ⊓
      ⨅ (w : Symmetrify Q) (b : w ⟶ Symmetrify.of.obj v),
        LinearMap.ker (LinearMap.mulLeft k (π (ofArrow (Quiver.reverse b))))) :
      ∃ t : k, x = t • y := by
    simp only [Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker,
      LinearMap.mulLeft_apply] at hx
    refine hz x ?_ hx.2
    rw [doubledVertexIdempotent_def]
    exact preprojectiveMk_vertexIdempotent_mul_of_mem_preprojectiveCorner hx.1
  split_ifs with h
  · obtain ⟨rfl, rfl⟩ := h
    refine (finrank_eq_one_iff' (K := k)).2 ⟨⟨y, Submodule.mem_inf.2 ⟨hy, (Submodule.mem_iInf _).2
      fun w => (Submodule.mem_iInf _).2 fun b => LinearMap.mem_ker.2 (hyb w b)⟩⟩,
      fun h => hy0 (congrArg Subtype.val h), fun x => ?_⟩
    obtain ⟨t, ht⟩ := hK x.2
    exact ⟨t, Subtype.ext ht.symm⟩
  · -- A nonzero multiple of `y` lies only in the graded corner `e_v Π_n e_u`.
    rw [Submodule.finrank_eq_zero, Submodule.eq_bot_iff]
    intro x hx
    obtain ⟨t, rfl⟩ := hK hx
    by_contra hx0
    have ht : t ≠ 0 := fun ht => hx0 (by rw [ht, zero_smul])
    have hy' : y ∈ preprojectiveCorner k Q m (Symmetrify.of.obj i) (Symmetrify.of.obj v) := by
      simpa [smul_smul, inv_mul_cancel₀ ht] using
        Submodule.smul_mem _ t⁻¹ (Submodule.mem_inf.1 hx).1
    refine hy0 (Submodule.disjoint_def.1 (disjoint_preprojectiveCorner ?_) y hy' hy)
    by_cases hmn : m = n
    · exact Or.inr (Or.inl fun hiu => h ⟨hmn, hiu⟩)
    · exact Or.inl hmn

/-- **The dimension recursion of a finite-dimensional preprojective algebra.** For every vertex `v`
there is a single pair `(n, u)` such that

```text
dim e_v Π_{m+2} e_i + dim e_v Π_m e_i = ∑_w #(w ⟶ v) dim e_w Π_{m+1} e_i + δ_{(m, i), (n, u)}
```

for every degree `m` and every vertex `i`, the sum running over the arrows of the doubled quiver
into `v`. Away from `(n, u)` this is the recursion of a Koszul algebra. -/
theorem exists_forall_finrank_preprojectiveCorner_add_two_add_finrank_preprojectiveCorner
    [DecidableEq Q] [FiniteDimensional k Π] (v : Q) :
    ∃ (n : ℕ) (u : Q), ∀ (m : ℕ) (i : Q),
      Module.finrank k
          (preprojectiveCorner k Q (m + 2) (Symmetrify.of.obj i) (Symmetrify.of.obj v)) +
          Module.finrank k (preprojectiveCorner k Q m (Symmetrify.of.obj i) (Symmetrify.of.obj v)) =
        ∑ w : Symmetrify Q, Fintype.card (w ⟶ Symmetrify.of.obj v) *
            Module.finrank k (preprojectiveCorner k Q (m + 1) (Symmetrify.of.obj i) w) +
          if m = n ∧ i = u then 1 else 0 := by
  obtain ⟨n, u, h⟩ := exists_forall_finrank_preprojectiveCorner_inf_iInf_ker_eq k v
  exact ⟨n, u, fun m i => by
    rw [finrank_preprojectiveCorner_add_two_add_finrank_preprojectiveCorner, h]⟩

end FiniteDimensional

end TauCeti
