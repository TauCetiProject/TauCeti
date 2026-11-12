/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Singular.Cubical.Based.Deformation
public import TauCeti.AlgebraicTopology.Singular.Cubical.Normalized
public import TauCeti.Data.Fin.Tuple.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.TransAt

/-!
# Homotopy classes of based cubes and the face relation

An `n`-cube that is `n`-based at `x` is a generalized loop in `Ω^ (Fin n) X x`
(`TauCeti.SingularCube.isBased_iff_mem_genLoop`), so it has a class in `π_n(X, x)`
(`TauCeti.SingularCube.basedClass`). For `n ≥ 2` these classes assemble into a homomorphism
`TauCeti.NormalizedCubicalChain.basedClassHom` from the normalized integral cubical `n`-chains to
`π_n(X, x)`, sending every cube that is not based to zero; it is well defined on normalized chains
because a degenerate based cube is constant.

The main result is the **face relation**: if an `(n + 1)`-cube `c` is `n`-based at `x`, its faces
are generalized loops, and

`Σᵢ (-1) ^ i ([face i 0 c] - [face i 1 c]) = 0` in `π_n(X, x)`,

that is, `basedClassHom` kills the boundary of `c`
(`TauCeti.NormalizedCubicalChain.basedClassHom_boundary_ofCube`), and hence the boundary of every
combination of based cubes (`TauCeti.NormalizedCubicalChain.basedClassHom_boundary_of_mem_span`).
So a combination of based cubes that is a boundary of based cubes has trivial class. This is the
relation needed to invert the Hurewicz map `π_n(X, x) → H_n(X; ℤ)` of an `(n - 1)`-connected space,
whose singular chains deform into combinations of based cubes.

## Proof of the face relation

Write `a = k` and `b = k + 1` for two adjacent coordinates. Precomposing `c` with the
reparametrisation `z ↦ z[a ↦ max(z_a, 2 z_b - 1), b ↦ min(1, 2 z_b)]` *caps* the face `b = 1`: the
new cube runs `c` at double speed in the coordinate `b` and then the face `b = 1`, swept along the
coordinate `a`. Its face `b = 1` is constant, its face `a = 0` is the concatenation of the old
face `a = 0` with the old face `b = 1`, and every other face is an old face concatenated with a
constant loop. As the face `b = 1` has sign `-(-1) ^ b = (-1) ^ a` in the alternating sum, the sum
is unchanged. Reflecting the coordinate `b` swaps the two faces in that coordinate and reverses
every other face in it, which negates the sum. Capping, reflecting and capping again therefore
makes both faces in the coordinate `b` constant without changing whether the sum vanishes. Doing
this for `b = n, n - 1, …, 1` leaves a cube whose faces outside the first coordinate are all
constant; such a cube is a homotopy relative to the boundary between its two faces in the first
coordinate, whose classes then agree.

The adjacent coordinates matter: the faces `a = 0` and `b = 1` share their parametrisation, so
the transfer involves no permutation of coordinates.

## Main definitions and results

* `TauCeti.SingularCube.basedClass`: the class in `π_n(X, x)` of an `n`-cube that is `n`-based at
  `x`, and of the constant loop for any other cube.
* `TauCeti.NormalizedCubicalChain.basedClassHom`: the homomorphism from normalized integral cubical
  `(n + 2)`-chains to `π_{n+2}(X, x)`.
* `TauCeti.NormalizedCubicalChain.basedClassHom_boundary_ofCube` and
  `TauCeti.NormalizedCubicalChain.basedClassHom_boundary_of_mem_span`: **the face relation**.

## References

* S. Eilenberg, *Singular homology theory*, Ann. of Math. (2) 45 (1944), 407–447, for the class in
  `π_n` of an `n`-chain of singular simplices sending the `(n - 1)`-skeleton to the base point,
  of which this is the cubical analogue.
* W. S. Massey, *Singular Homology Theory*, GTM 70, Springer, 1980, Chapter II, for singular cubes,
  their faces and normalized cubical chains.
-/

public section

noncomputable section

open scoped unitInterval Topology Topology.Homotopy

namespace TauCeti

variable {X : Type*} [TopologicalSpace X] {x : X}

namespace SingularCube

/-! ### The class of a based cube -/

open scoped Classical in
/-- The class in `π_n(X, x)` of a singular `n`-cube that is `n`-based at `x`, that is, of a
generalized loop at `x` (`TauCeti.SingularCube.isBased_iff_mem_genLoop`). Every other `n`-cube is
sent to the class of the constant loop. -/
def basedClass (x : X) {n : ℕ} (c : SingularCube X n) : HomotopyGroup (Fin n) X x :=
  if h : c.IsBased n x then ⟦⟨c, isBased_iff_mem_genLoop.1 h⟩⟧ else ⟦GenLoop.const⟧

theorem basedClass_of_isBased {n : ℕ} {c : SingularCube X n} (h : c.IsBased n x) :
    basedClass x c = ⟦⟨c, isBased_iff_mem_genLoop.1 h⟩⟧ :=
  dite_eq_left_of_eq_true (eq_true h)

theorem basedClass_of_not_isBased {n : ℕ} {c : SingularCube X n} (h : ¬ c.IsBased n x) :
    basedClass x c = ⟦GenLoop.const⟧ :=
  dite_eq_right_of_eq_false (eq_false h)

/-- The class of a generalized loop, read as a singular cube, is its homotopy class. -/
@[simp]
theorem basedClass_coe {n : ℕ} (p : Ω^ (Fin n) X x) : basedClass x (p : SingularCube X n) = ⟦p⟧ :=
  basedClass_of_isBased (isBased_iff_mem_genLoop.2 p.2)

/-- The constant cube at `x` has the class of the constant loop. -/
@[simp]
theorem basedClass_const {n : ℕ} :
    basedClass x (ContinuousMap.const (Fin n → I) x) = ⟦GenLoop.const⟧ :=
  basedClass_coe (GenLoop.const : Ω^ (Fin n) X x)

/-- A degenerate cube has the class of the constant loop: if it is based, it is constant. -/
theorem basedClass_of_isDegenerate {n : ℕ} {c : SingularCube X n} (hc : c.IsDegenerate) :
    basedClass x c = ⟦GenLoop.const⟧ := by
  by_cases h : c.IsBased n x
  · obtain ⟨i, hi⟩ := isDegenerate_iff.1 hc
    have : (⟨c, isBased_iff_mem_genLoop.1 h⟩ : Ω^ (Fin n) X x) = GenLoop.const := by
      refine GenLoop.ext _ _ fun y ↦ ?_
      rw [GenLoop.mk_apply, GenLoop.const_apply, ← hi.apply_update y 0]
      exact isBased_iff_mem_genLoop.1 h _ ⟨i, .inl (Function.update_self ..)⟩
    rw [basedClass_of_isBased h, this]
  · exact basedClass_of_not_isBased h

/-! ### Reparametrising one coordinate -/

/-- `t ↦ 2t`, clamped to the unit interval. -/
private def dbl (t : I) : I := Set.projIcc 0 1 zero_le_one (2 * t)

/-- `t ↦ 2t - 1`, clamped to the unit interval. -/
private def dblSub (t : I) : I := Set.projIcc 0 1 zero_le_one (2 * t - 1)

private lemma continuous_dbl : Continuous dbl := by unfold dbl; fun_prop

private lemma continuous_dblSub : Continuous dblSub := by unfold dblSub; fun_prop

@[simp] private lemma dbl_zero : dbl 0 = 0 := by
  simp [dbl]

@[simp] private lemma dbl_one : dbl 1 = 1 := by
  simp [dbl, Set.projIcc_of_right_le]

@[simp] private lemma dblSub_zero : dblSub 0 = 0 := by
  simp [dblSub, Set.projIcc_of_le_left]

@[simp] private lemma dblSub_one : dblSub 1 = 1 := by
  norm_num [dblSub, Set.projIcc_of_right_le]

private lemma coe_dbl_of_le {t : I} (h : (t : ℝ) ≤ 1 / 2) : (dbl t : ℝ) = 2 * t := by
  rw [dbl, Set.projIcc_of_mem _ ⟨by linarith [t.2.1], by linarith⟩]

private lemma dbl_of_lt {t : I} (h : 1 / 2 < (t : ℝ)) : dbl t = 1 := by
  rw [dbl, Set.projIcc_of_right_le _ (by linarith)]; rfl

private lemma dblSub_of_le {t : I} (h : (t : ℝ) ≤ 1 / 2) : dblSub t = 0 := by
  rw [dblSub, Set.projIcc_of_le_left _ (by linarith)]; rfl

private lemma coe_dblSub_of_lt {t : I} (h : 1 / 2 < (t : ℝ)) :
    (dblSub t : ℝ) = 2 * t - 1 := by
  rw [dblSub, Set.projIcc_of_mem _ ⟨by linarith, by linarith [t.2.2]⟩]

@[simp] private lemma max_one (t : I) : max t 1 = 1 := max_eq_right unitInterval.le_one'

@[simp] private lemma one_max (t : I) : max 1 t = 1 := max_eq_left unitInterval.le_one'

/-! ### Cubes whose faces are generalized loops -/

/-- The faces of `c` at both ends of every coordinate are generalized loops at `x`. For an
`(m + 1)`-cube this amounts to being `m`-based at `x`; it is the form in which the hypothesis is
checked after reparametrising, from the faces alone. -/
private def FacesBased (x : X) {m : ℕ} (c : SingularCube X (m + 1)) : Prop :=
  ∀ (j : Fin (m + 1)) (t : I), (t = 0 ∨ t = 1) → face j t c ∈ GenLoop (Fin m) X x

/-- A cube whose faces are generalized loops sends every point with two coordinates at an end of
the interval to `x`. -/
private lemma FacesBased.apply_eq {m : ℕ} {c : SingularCube X (m + 1)} (hc : FacesBased x c)
    {z : Fin (m + 1) → I} {i j : Fin (m + 1)} (hij : i ≠ j) (hi : z i = 0 ∨ z i = 1)
    (hj : z j = 0 ∨ z j = 1) : c z = x := by
  obtain ⟨l, rfl⟩ := Fin.exists_succAbove_eq hij.symm
  have := hc i (z i) hi (i.removeNth z) ⟨l, by simpa [Fin.removeNth_apply] using hj⟩
  rwa [face_apply, Fin.insertNth_self_removeNth] at this

/-- The face of a cube whose faces are generalized loops, as a generalized loop. -/
private def FacesBased.loop {m : ℕ} {c : SingularCube X (m + 1)} (hc : FacesBased x c)
    (j : Fin (m + 1)) {t : I} (ht : t = 0 ∨ t = 1) : Ω^ (Fin m) X x :=
  ⟨face j t c, hc j t ht⟩

@[simp]
private lemma FacesBased.loop_apply {m : ℕ} {c : SingularCube X (m + 1)} (hc : FacesBased x c)
    (j : Fin (m + 1)) {t : I} (ht : t = 0 ∨ t = 1) (y : Fin m → I) :
    hc.loop j ht y = c (j.insertNth t y) :=
  face_apply j t c y

private lemma FacesBased.basedClass_face {m : ℕ} {c : SingularCube X (m + 1)}
    (hc : FacesBased x c) (j : Fin (m + 1)) {t : I} (ht : t = 0 ∨ t = 1) :
    basedClass x (face j t c) = ⟦hc.loop j ht⟧ :=
  basedClass_coe (hc.loop j ht)

/-- A cube one of whose faces is constant at `x` sends every point of that face to `x`. -/
private lemma apply_eq_of_face_eq_const {m : ℕ} {c : SingularCube X (m + 1)} {j : Fin (m + 1)}
    {t : I} (h : face j t c = ContinuousMap.const _ x) {w : Fin (m + 1) → I} (hw : w j = t) :
    c w = x := by
  subst hw
  simpa [Fin.insertNth_self_removeNth] using congrArg (fun f ↦ f (j.removeNth w)) h

/-! ### Capping a face -/

/-- The reparametrisation of `Iᵐ⁺¹` that runs a cube at double speed in the coordinate `k.succ`
and then its face `k.succ = 1`, swept by `max` along the coordinate `k.castSucc`. -/
private def capMap {m : ℕ} (k : Fin m) : C(Fin (m + 1) → I, Fin (m + 1) → I) where
  toFun z := Function.update
    (Function.update z k.castSucc (max (z k.castSucc) (dblSub (z k.succ)))) k.succ
    (dbl (z k.succ))
  continuous_toFun :=
    (continuous_id.update _ ((continuous_apply k.castSucc).max
      (continuous_dblSub.comp (continuous_apply k.succ)))).update _
      (continuous_dbl.comp (continuous_apply k.succ))

private lemma capMap_apply {m : ℕ} (k : Fin m) (z : Fin (m + 1) → I) :
    capMap k z = Function.update
      (Function.update z k.castSucc (max (z k.castSucc) (dblSub (z k.succ)))) k.succ
      (dbl (z k.succ)) :=
  rfl

section Cap

variable {m : ℕ} {c : SingularCube X (m + 1)}

private lemma face_succ_zero_comp_capMap (k : Fin m) :
    face k.succ 0 (c.comp (capMap k)) = face k.succ 0 c := by
  ext y
  simp [capMap_apply, -Fin.insertNth_succ_apply_castSucc]

private lemma face_succ_one_comp_capMap (hc : FacesBased x c) (k : Fin m) :
    face k.succ 1 (c.comp (capMap k)) = ContinuousMap.const _ x := by
  ext y
  simp only [face_apply, ContinuousMap.comp_apply, capMap_apply, Fin.insertNth_apply_same,
    dbl_one, dblSub_one, max_one, ContinuousMap.const_apply]
  have hk : k.castSucc ≠ k.succ := Fin.castSucc_lt_succ.ne
  exact hc.apply_eq hk (.inr (by rw [Function.update_of_ne hk, Function.update_self]))
    (.inr (Function.update_self ..))

private lemma face_castSucc_zero_comp_capMap (hc : FacesBased x c) (k : Fin m) :
    face k.castSucc 0 (c.comp (capMap k)) =
      (GenLoop.transAt k (hc.loop k.castSucc (.inl rfl)) (hc.loop k.succ (.inr rfl)) :
        SingularCube X m) := by
  ext y
  rcases le_or_gt (y k : ℝ) (1 / 2) with h | h
  · rw [GenLoop.coe_coe, GenLoop.transAt_apply_of_le k _ _ h (coe_dbl_of_le h)]
    simp [capMap_apply, dblSub_of_le h]
  · rw [GenLoop.coe_coe, GenLoop.transAt_apply_of_lt k _ _ h (coe_dblSub_of_lt h)]
    simp [capMap_apply, dbl_of_lt h, Fin.update_insertNth_castSucc]

private lemma face_castSucc_one_comp_capMap (hc : FacesBased x c) (k : Fin m) :
    face k.castSucc 1 (c.comp (capMap k)) =
      (GenLoop.transAt k (hc.loop k.castSucc (.inr rfl)) GenLoop.const : SingularCube X m) := by
  ext y
  rcases le_or_gt (y k : ℝ) (1 / 2) with h | h
  · rw [GenLoop.coe_coe, GenLoop.transAt_apply_of_le k _ _ h (coe_dbl_of_le h)]
    simp [capMap_apply]
  · rw [GenLoop.coe_coe, GenLoop.transAt_apply_of_lt k _ _ h (coe_dblSub_of_lt h),
      GenLoop.const_apply]
    have hk : k.castSucc ≠ k.succ := Fin.castSucc_lt_succ.ne
    simp only [face_apply, ContinuousMap.comp_apply, capMap_apply, Fin.insertNth_apply_same,
      one_max, Fin.update_insertNth, Fin.insertNth_castSucc_apply_succ, dbl_of_lt h]
    exact hc.apply_eq hk (.inr (by rw [Function.update_of_ne hk, Fin.insertNth_apply_same]))
      (.inr (Function.update_self ..))

private lemma face_comp_capMap_of_ne (hc : FacesBased x c) (k : Fin m) {j : Fin (m + 1)}
    {l : Fin m} (hjl : j.succAbove l = k.succ) (hj : j ≠ k.castSucc) {t : I}
    (ht : t = 0 ∨ t = 1) :
    face j t (c.comp (capMap k)) =
      (GenLoop.transAt l (hc.loop j ht) GenLoop.const : SingularCube X m) := by
  ext y
  have hb : (j.insertNth t y : Fin (m + 1) → I) k.succ = y l := by
    rw [← hjl, Fin.insertNth_apply_succAbove]
  rcases le_or_gt (y l : ℝ) (1 / 2) with h | h
  · rw [GenLoop.coe_coe, GenLoop.transAt_apply_of_le l _ _ h (coe_dbl_of_le h)]
    simp [capMap_apply, hb, dblSub_of_le h, hjl]
  · rw [GenLoop.coe_coe, GenLoop.transAt_apply_of_lt l _ _ h (coe_dblSub_of_lt h),
      GenLoop.const_apply]
    have hjb : j ≠ k.succ := hjl ▸ (Fin.succAbove_ne j l).symm
    simp only [face_apply, ContinuousMap.comp_apply, capMap_apply, hb, dbl_of_lt h]
    exact hc.apply_eq hjb
      (by rw [Function.update_of_ne hjb, Function.update_of_ne hj, Fin.insertNth_apply_same]
          exact ht)
      (.inr (Function.update_self ..))

/-- The reflection of `Iᵐ` in its `i`-th coordinate. -/
private def reflectMap {m : ℕ} (i : Fin m) : C(Fin m → I, Fin m → I) where
  toFun z := Function.update z i (σ (z i))
  continuous_toFun :=
    continuous_id.update _ (unitInterval.continuous_symm.comp (continuous_apply i))

private lemma reflectMap_apply {m : ℕ} (i : Fin m) (z : Fin m → I) :
    reflectMap i z = Function.update z i (σ (z i)) :=
  rfl

private lemma face_comp_reflectMap_self (i : Fin (m + 1)) (t : I) :
    face i t (c.comp (reflectMap i)) = face i (σ t) c := by
  ext y
  simp [reflectMap_apply]

private lemma face_comp_reflectMap_of_ne (hc : FacesBased x c) {i j : Fin (m + 1)} {l : Fin m}
    (hjl : j.succAbove l = i) {t : I} (ht : t = 0 ∨ t = 1) :
    face j t (c.comp (reflectMap i)) = (GenLoop.symmAt l (hc.loop j ht) : SingularCube X m) := by
  ext y
  rw [GenLoop.coe_coe, GenLoop.symmAt_apply]
  subst hjl
  simp [reflectMap_apply]

private lemma FacesBased.comp_capMap (hc : FacesBased x c) (k : Fin m) :
    FacesBased x (c.comp (capMap k)) := by
  intro j t ht
  by_cases hja : j = k.castSucc
  · subst hja
    rcases ht with rfl | rfl
    · rw [face_castSucc_zero_comp_capMap hc]; exact Subtype.property _
    · rw [face_castSucc_one_comp_capMap hc]; exact Subtype.property _
  by_cases hjb : j = k.succ
  · subst hjb
    rcases ht with rfl | rfl
    · rw [face_succ_zero_comp_capMap]; exact hc _ _ (.inl rfl)
    · rw [face_succ_one_comp_capMap hc]; exact GenLoop.const.2
  obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq (Ne.symm hjb)
  rw [face_comp_capMap_of_ne hc k hl hja ht]
  exact Subtype.property _

private lemma capMap_apply_of_ne (k : Fin m) {z : Fin (m + 1) → I} {j : Fin (m + 1)}
    (hja : j ≠ k.castSucc) (hjb : j ≠ k.succ) : capMap k z j = z j := by
  rw [capMap_apply, Function.update_of_ne hjb, Function.update_of_ne hja]

private lemma FacesBased.comp_reflectMap (hc : FacesBased x c) (i : Fin (m + 1)) :
    FacesBased x (c.comp (reflectMap i)) := by
  intro j t ht
  by_cases hji : j = i
  · subst hji
    rw [face_comp_reflectMap_self]
    exact hc _ _ (by rcases ht with rfl | rfl <;> simp)
  obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq (Ne.symm hji)
  rw [face_comp_reflectMap_of_ne hc hl ht]
  exact Subtype.property _

private lemma reflectMap_apply_of_ne {i j : Fin m} {z : Fin m → I} (hji : j ≠ i) :
    reflectMap i z j = z j := by
  rw [reflectMap_apply, Function.update_of_ne hji]

/-- If the faces of a cube in every coordinate but the first are constant at `x`, then the cube is
a homotopy relative to the boundary between its two faces in the first coordinate. -/
private lemma homotopic_loop_zero (hc : FacesBased x c)
    (h : ∀ j : Fin (m + 1), j ≠ 0 → ∀ t : I, (t = 0 ∨ t = 1) → face j t c = .const _ x) :
    GenLoop.Homotopic (hc.loop 0 (.inl rfl)) (hc.loop 0 (.inr rfl)) :=
  ⟨{ toFun p := c (Fin.insertNth 0 p.1 p.2)
     continuous_toFun := by fun_prop
     map_zero_left y := (hc.loop_apply 0 (.inl rfl) y).symm
     map_one_left y := (hc.loop_apply 0 (.inr rfl) y).symm
     prop' s y hy := by
       obtain ⟨l, hl⟩ := hy
       refine (apply_eq_of_face_eq_const (h l.succ (Fin.succ_ne_zero l) (y l) hl) ?_).trans
         (GenLoop.boundary _ y ⟨l, hl⟩).symm
       simp }⟩

end Cap

/-! ### The alternating sum of the classes of the faces -/

section FaceSum

variable {n : ℕ}

/-- The signed classes of the two faces of a cube in the coordinate `j`. -/
private def faceTerm (x : X) (c : SingularCube X (n + 3)) (j : Fin (n + 3)) :
    Additive (HomotopyGroup (Fin (n + 2)) X x) :=
  (-1 : ℤ) ^ (j : ℕ) • (Additive.ofMul (basedClass x (face j 0 c)) -
    Additive.ofMul (basedClass x (face j 1 c)))

/-- Capping does not change the alternating sum of the classes of the faces. -/
private lemma sum_faceTerm_comp_capMap {c : SingularCube X (n + 3)} (hc : FacesBased x c)
    (k : Fin (n + 2)) : ∑ j, faceTerm x (c.comp (capMap k)) j = ∑ j, faceTerm x c j := by
  rw [← sub_eq_zero, ← Finset.sum_sub_distrib,
    Fintype.sum_eq_add k.castSucc k.succ Fin.castSucc_lt_succ.ne]
  · simp only [faceTerm, face_castSucc_zero_comp_capMap hc, face_castSucc_one_comp_capMap hc,
      face_succ_zero_comp_capMap, face_succ_one_comp_capMap hc, basedClass_coe,
      HomotopyGroup.ofMul_transAt, basedClass_const, HomotopyGroup.ofMul_const, Fin.val_succ,
      Fin.val_castSucc, pow_succ]
    simp only [hc.basedClass_face, or_true, true_or]
    module
  · rintro j ⟨hja, hjb⟩
    obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hjb.symm
    simp only [faceTerm, face_comp_capMap_of_ne hc k hl hja (.inl rfl),
      face_comp_capMap_of_ne hc k hl hja (.inr rfl), basedClass_coe, HomotopyGroup.ofMul_transAt,
      HomotopyGroup.ofMul_const, zero_add, hc.basedClass_face, or_true, true_or, sub_self]

/-- Reflecting a coordinate negates the alternating sum of the classes of the faces. -/
private lemma sum_faceTerm_comp_reflectMap {c : SingularCube X (n + 3)} (hc : FacesBased x c)
    (i : Fin (n + 3)) : ∑ j, faceTerm x (c.comp (reflectMap i)) j = -∑ j, faceTerm x c j := by
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hji : j = i
  · subst hji
    simp only [faceTerm, face_comp_reflectMap_self, unitInterval.symm_zero,
      unitInterval.symm_one]
    module
  obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq (Ne.symm hji)
  simp only [faceTerm, face_comp_reflectMap_of_ne hc hl (.inl rfl),
    face_comp_reflectMap_of_ne hc hl (.inr rfl), basedClass_coe, HomotopyGroup.ofMul_symmAt,
    hc.basedClass_face, or_true, true_or]
  module

/-- The alternating sum vanishes when the faces in every coordinate but the first are constant. -/
private lemma sum_faceTerm_eq_zero_of_face_eq_const {c : SingularCube X (n + 3)}
    (hc : FacesBased x c)
    (h : ∀ j : Fin (n + 3), j ≠ 0 → ∀ t : I, (t = 0 ∨ t = 1) → face j t c = .const _ x) :
    ∑ j, faceTerm x c j = 0 := by
  rw [Fin.sum_univ_succ, Finset.sum_eq_zero fun j _ ↦ ?_, add_zero]
  · have : (⟦hc.loop 0 (.inl rfl)⟧ : HomotopyGroup (Fin (n + 2)) X x) = ⟦hc.loop 0 (.inr rfl)⟧ :=
      Quotient.sound (homotopic_loop_zero hc h)
    simp only [faceTerm, hc.basedClass_face, or_true, true_or, Fin.val_zero, pow_zero, one_smul]
    rw [this, sub_self]
  · simp only [faceTerm, h j.succ (Fin.succ_ne_zero j) _ (.inl rfl),
      h j.succ (Fin.succ_ne_zero j) _ (.inr rfl), basedClass_const, sub_self, smul_zero]

/-- The alternating sum vanishes when the faces in every coordinate after the `k`-th are constant:
induction on `k`, capping both faces in the coordinate `k`. -/
private lemma sum_faceTerm_eq_zero_aux (k : ℕ) (c : SingularCube X (n + 3)) (hc : FacesBased x c)
    (h : ∀ j : Fin (n + 3), k < (j : ℕ) → ∀ t : I, (t = 0 ∨ t = 1) → face j t c = .const _ x) :
    ∑ j, faceTerm x c j = 0 := by
  induction k generalizing c with
  | zero =>
    exact sum_faceTerm_eq_zero_of_face_eq_const hc fun j hj ↦
      h j (Nat.pos_of_ne_zero (Fin.val_ne_iff.2 hj))
  | succ k ih =>
    by_cases hk : k < n + 2
    swap
    · exact ih c hc fun j hj ↦ absurd j.2 (by omega)
    let K : Fin (n + 2) := ⟨k, hk⟩
    -- Cap the face `K.succ = 1`, swap the two faces in the coordinate `K.succ`, and cap again.
    have hc₁ := hc.comp_capMap K
    have hc₂ := hc₁.comp_reflectMap K.succ
    have key := ih _ (hc₂.comp_capMap K) fun j hj t ht ↦ by
      rcases (show (j : ℕ) = k + 1 ∨ k + 1 < j by omega) with hj' | hj'
      · obtain rfl : j = K.succ := Fin.ext hj'
        rcases ht with rfl | rfl
        · rw [face_succ_zero_comp_capMap, face_comp_reflectMap_self, unitInterval.symm_zero,
            face_succ_one_comp_capMap hc]
        · exact face_succ_one_comp_capMap hc₂ K
      · have hja : j ≠ K.castSucc := Fin.ne_of_val_ne (by simp [K]; omega)
        have hjb : j ≠ K.succ := Fin.ne_of_val_ne (by simp [K]; omega)
        ext y
        simp only [face_apply, ContinuousMap.comp_apply, ContinuousMap.const_apply]
        refine apply_eq_of_face_eq_const (h j hj' t ht) ?_
        simp [capMap_apply_of_ne K hja hjb, reflectMap_apply_of_ne hjb]
    rwa [sum_faceTerm_comp_capMap hc₂, sum_faceTerm_comp_reflectMap hc₁,
      sum_faceTerm_comp_capMap hc, neg_eq_zero] at key

/-- **The face relation.** The faces of a cube that is `(n + 2)`-based at `x` are generalized loops,
and the alternating sum of their classes vanishes in `π_{n+2}(X, x)`. -/
private lemma sum_faceTerm_eq_zero {c : SingularCube X (n + 3)} (hc : c.IsBased (n + 2) x) :
    ∑ j, faceTerm x c j = 0 :=
  sum_faceTerm_eq_zero_aux (n + 2) c (fun j _ ht ↦ isBased_iff_mem_genLoop.1 (hc.face j ht))
    fun j hj ↦ absurd j.2 (by omega)

end FaceSum

end SingularCube

namespace NormalizedCubicalChain

open SingularCube

/-- The homomorphism from the normalized integral cubical `(n + 2)`-chains of `X` to
`π_{n+2}(X, x)` that sends the class of an `(n + 2)`-based cube, a generalized loop, to its
homotopy class (`TauCeti.SingularCube.basedClass`), and the class of every other cube to zero. It
is well defined on normalized chains because a degenerate based cube is constant. -/
def basedClassHom (x : X) (n : ℕ) :
    NormalizedCubicalChain X ℤ (n + 2) →ₗ[ℤ] Additive (HomotopyGroup (Fin (n + 2)) X x) :=
  (CubicalChain.degenerate X ℤ (n + 2)).liftQ
    (Finsupp.linearCombination ℤ fun c ↦ Additive.ofMul (basedClass x c)) <| by
      rw [CubicalChain.degenerate_def, Submodule.span_le]
      rintro _ ⟨c, hc, rfl⟩
      simp [basedClass_of_isDegenerate hc, HomotopyGroup.ofMul_const]

@[simp]
theorem basedClassHom_ofCube {n : ℕ} (c : SingularCube X (n + 2)) :
    basedClassHom x n (ofCube X ℤ c) = Additive.ofMul (basedClass x c) := by
  simp [basedClassHom, ofCube_def]

/-- An `(n + 2)`-based cube is sent to its class as a generalized loop. -/
theorem basedClassHom_ofCube_of_isBased {n : ℕ} {c : SingularCube X (n + 2)}
    (hc : c.IsBased (n + 2) x) :
    basedClassHom x n (ofCube X ℤ c) =
      Additive.ofMul (α := HomotopyGroup (Fin (n + 2)) X x)
        ⟦⟨c, isBased_iff_mem_genLoop.1 hc⟩⟧ := by
  rw [basedClassHom_ofCube, basedClass_of_isBased hc]

/-- A cube that is not `(n + 2)`-based is sent to zero. -/
theorem basedClassHom_ofCube_of_not_isBased {n : ℕ} {c : SingularCube X (n + 2)}
    (hc : ¬ c.IsBased (n + 2) x) : basedClassHom x n (ofCube X ℤ c) = 0 := by
  rw [basedClassHom_ofCube, basedClass_of_not_isBased hc, HomotopyGroup.ofMul_const]

/-- **Boundaries of based cubes have trivial class**: the boundary of an `(n + 2)`-based
`(n + 3)`-cube is sent to zero in `π_{n+2}(X, x)`. Equivalently, the alternating sum of the classes
of its faces, which are generalized loops, vanishes. -/
theorem basedClassHom_boundary_ofCube {n : ℕ} {c : SingularCube X (n + 3)}
    (hc : c.IsBased (n + 2) x) : basedClassHom x n (boundary X ℤ (n + 2) (ofCube X ℤ c)) = 0 := by
  simpa [faceTerm] using sum_faceTerm_eq_zero hc

/-- The boundary of a combination of `(n + 2)`-based `(n + 3)`-cubes is sent to zero in
`π_{n+2}(X, x)`. -/
theorem basedClassHom_boundary_of_mem_span {n : ℕ} {g : NormalizedCubicalChain X ℤ (n + 3)}
    (hg : g ∈ Submodule.span ℤ (ofCube X ℤ '' {c | c.IsBased (n + 2) x})) :
    basedClassHom x n (boundary X ℤ (n + 2) g) = 0 := by
  induction hg using Submodule.span_induction with
  | mem _ h =>
    obtain ⟨c, hc, rfl⟩ := h
    exact basedClassHom_boundary_ofCube hc
  | zero => simp
  | add _ _ _ _ ha hb => simp [ha, hb]
  | smul a _ _ h => simp [h]

end NormalizedCubicalChain

end TauCeti
