/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Stable
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.CentralExtension
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.RootSubgroup

/-!
# Stable Steinberg groups and the Kervaire–Steinberg universal central extension

For an associative unital ring `R`, the finite-rank Steinberg groups `SteinbergGroup (Fin n) R`
form a directed system along stabilization `SteinbergGroup.stabilize R h`. The canonical inclusions
`ofFin R n : SteinbergGroup (Fin n) R →* SteinbergGroup ℕ R` assemble into a group isomorphism
`directLimitEquiv R` identifying `DirectLimit (SteinbergGroup (Fin ·) R)` with `SteinbergGroup ℕ R`.

The finite-rank homomorphisms `toGL (Fin n) R : SteinbergGroup (Fin n) R →* GL (Fin n) R` are
compatible with matrix stabilization `TauCeti.stabilizeGL` and therefore descend to the canonical
homomorphism `toStableGL R : SteinbergGroup ℕ R →* StableGeneralLinearGroup R`, whose image is the
stable elementary subgroup `TauCeti.StableGeneralLinearGroup.elementarySubgroup R`.

Using the faithful column and row root subgroups from
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.RootSubgroup`, any element of
`ker (toGL (Fin m) R)` becomes central after stabilizing to any strictly larger rank `n > m`.
Passing to the limit shows that `ker (toStableGL R)` is central in `SteinbergGroup ℕ R`; conversely,
any central element of `SteinbergGroup ℕ R` maps to a matrix commuting with all elementary matrices
after stabilization and is therefore `1`, so
`ker (toStableGL R) = Subgroup.center (SteinbergGroup ℕ R)`.
Combining centrality with the central-extension lifting theorem from
`TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.CentralExtension` establishes the
Kervaire–Steinberg theorem: `toStableElementary R : SteinbergGroup ℕ R →* E_∞(R)` is a universal
central extension.

## Main definitions

* `TauCeti.SteinbergGroup.ofFin`: the canonical inclusion `St_n(R) →* St(R)`.
* `TauCeti.SteinbergGroup.directLimitEquiv`: the isomorphism
  `DirectLimit (SteinbergGroup (Fin ·) R) ≃* SteinbergGroup ℕ R`.
* `TauCeti.SteinbergGroup.toStableGL`: the canonical homomorphism `St(R) →* GL_∞(R)`.
* `TauCeti.SteinbergGroup.toStableElementary`: the canonical surjection `St(R) →* E_∞(R)`.

## Main results

* `TauCeti.SteinbergGroup.toGL_stabilize`: `toGL` commutes with stabilization.
* `TauCeti.SteinbergGroup.stabilize_mem_center_of_mem_ker_toGL`: stabilizing an element of
  `ker (toGL (Fin m) R)` to any rank `n > m` makes it central.
* `TauCeti.SteinbergGroup.range_toStableGL`: the image of `toStableGL R` is `E_∞(R)`.
* `TauCeti.SteinbergGroup.ker_toStableGL_eq_center`: `ker (toStableGL R)` equals the entire center
  of `SteinbergGroup ℕ R`.
* `TauCeti.SteinbergGroup.ker_toGL_le_center_of_injOn_ofFin`: if `ofFin R n` is injective on
  `ker (toGL (Fin n) R)`, then `ker (toGL (Fin n) R)` is central in `SteinbergGroup (Fin n) R`.
* `TauCeti.SteinbergGroup.isUniversalCentralExtension_toStableElementary`: Kervaire–Steinberg's
  theorem that `toStableElementary R : St(R) →* E_∞(R)` is a universal central extension.
* `TauCeti.SteinbergGroup.existsUnique_lift_toStableGL`: direct universal-property formulation for
  central extensions `q : E →* GL_∞(R)` with image `E_∞(R)`.

## References

* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5,
  Theorem 5.1 and Corollary 5.8.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Theorem 5.2.1 and Theorem 5.5.
-/

public section

noncomputable section

open Matrix

open scoped commutatorElement

namespace TauCeti

namespace SteinbergGroup

variable {R : Type*} [Ring R]

/-! ## Stabilization compatibility with `toGL` -/

/-- `toGL` commutes with stabilization of finite-rank Steinberg groups. -/
theorem toGL_stabilize {m n : ℕ} (h : m ≤ n) (x : SteinbergGroup (Fin m) R) :
    toGL (Fin n) R (stabilize R h x) = stabilizeGL R h (toGL (Fin m) R x) := by
  induction x using SteinbergGroup.induction with
  | one => simp
  | of hij a =>
    rw [stabilize_of, toGL_of, toGL_of, stabilizeGL_transvectionUnit]
  | mul x y hx hy => simp [hx, hy]

/-- Stabilizing an element of `ker (toGL (Fin m) R)` to any strictly larger rank `n > m` produces
a central element of `SteinbergGroup (Fin n) R`. -/
theorem stabilize_mem_center_of_mem_ker_toGL {m n : ℕ} (h : m < n) {w : SteinbergGroup (Fin m) R}
    (hw : toGL (Fin m) R w = 1) :
    stabilize R h.le w ∈ Subgroup.center (SteinbergGroup (Fin n) R) := by
  have hstab : stabilize R h.le = reindex R (Fin.castLE h.le) (Fin.castLE_injective h.le) := by
    refine hom_ext fun hij a => ?_
    rw [stabilize_of, reindex_of]
  rw [hstab]
  refine reindex_mem_center_of_toGL_eq_one (Fin.castLE h.le) (Fin.castLE_injective h.le)
    ⟨⟨m, h⟩, fun k hk => ?_⟩ ?_
  · have hval := congrArg Fin.val hk
    simp only [Fin.val_castLE] at hval
    exact absurd hval (ne_of_lt k.isLt)
  · rw [← hstab, toGL_stabilize, hw, map_one]

/-! ## Direct-limit presentation of `SteinbergGroup ℕ R` -/

variable (R) in
/-- The canonical inclusion `St_n(R) →* St(R)` sending `xᵢⱼ(a)` (`i, j : Fin n`) to
`x_{i.val, j.val}(a)`. -/
def ofFin (n : ℕ) : SteinbergGroup (Fin n) R →* SteinbergGroup ℕ R :=
  reindex R Fin.val Fin.val_injective

/-- `ofFin` sends each finite-rank root generator to the corresponding generator of `St(R)`. -/
@[simp]
theorem ofFin_of (n : ℕ) {i j : Fin n} (hij : i ≠ j) (a : R) :
    ofFin R n (of hij a) = of (Fin.val_injective.ne hij) a :=
  reindex_of Fin.val Fin.val_injective hij a

/-- Composition form of `ofFin_stabilize`. -/
theorem ofFin_comp_stabilize {m n : ℕ} (h : m ≤ n) :
    (ofFin R n).comp (stabilize R h) = ofFin R m := by
  refine hom_ext fun hij a => ?_
  simp

/-- The inclusions `ofFin` are compatible with stabilization. -/
@[simp]
theorem ofFin_stabilize {m n : ℕ} (h : m ≤ n) (x : SteinbergGroup (Fin m) R) :
    ofFin R n (stabilize R h x) = ofFin R m x :=
  DFunLike.congr_fun (ofFin_comp_stabilize h) x

/-- `ofFin` commutes with ring homomorphisms. -/
theorem ofFin_map {S : Type*} [Ring S] (f : R →+* S) (n : ℕ) (x : SteinbergGroup (Fin n) R) :
    ofFin S n (map f x) = map f (ofFin R n x) :=
  reindex_map Fin.val Fin.val_injective f x

/-- Auxiliary generator image in `DirectLimit (SteinbergGroup (Fin ·) R)`. -/
private def directLimitGen {i j : ℕ} (hij : i ≠ j) (a : R) :
    DirectLimit (fun n : ℕ => SteinbergGroup (Fin n) R) fun _ _ h => stabilize R h :=
  DirectLimit.Monoid.of (fun n : ℕ => SteinbergGroup (Fin n) R) (fun _ _ h => stabilize R h)
    (max i j + 1)
    (of (i := ⟨i, by omega⟩) (j := ⟨j, by omega⟩) (by simpa [Fin.ext_iff]) a)

/-- `directLimitGen hij a` equals the image of `of hij a` from any rank `m` containing `i` and
`j`. -/
private theorem directLimitGen_eq_of {i j : ℕ} (hij : i ≠ j) (a : R) {m : ℕ}
    (hi : i < m) (hj : j < m) :
    directLimitGen hij a =
      DirectLimit.Monoid.of (fun n : ℕ => SteinbergGroup (Fin n) R) (fun _ _ h => stabilize R h) m
        (of (i := ⟨i, hi⟩) (j := ⟨j, hj⟩) (by simpa [Fin.ext_iff]) a) := by
  have hle : max i j + 1 ≤ m := by omega
  rw [directLimitGen, ← DirectLimit.Monoid.of_f (G := fun n : ℕ => SteinbergGroup (Fin n) R)
    (f := fun _ _ h => stabilize R h) hle, stabilize_of]

private theorem directLimitGen_add {i j : ℕ} (hij : i ≠ j) (a b : R) :
    directLimitGen hij a * directLimitGen hij b = directLimitGen hij (a + b) := by
  simp only [directLimitGen, ← map_mul, of_mul_of]

private theorem directLimitGen_comm {i j k l : ℕ} (hij : i ≠ j) (hkl : k ≠ l)
    (hjk : j ≠ k) (hil : i ≠ l) (a b : R) :
    Commute (directLimitGen hij a) (directLimitGen hkl b) := by
  set m := max (max i j) (max k l) + 1
  rw [directLimitGen_eq_of hij a (m := m) (by omega) (by omega),
    directLimitGen_eq_of hkl b (m := m) (by omega) (by omega)]
  exact (commute_of (i := (⟨i, by omega⟩ : Fin m)) (j := ⟨j, by omega⟩)
    (k := ⟨k, by omega⟩) (l := ⟨l, by omega⟩) (by simpa [Fin.ext_iff]) (by simpa [Fin.ext_iff])
    (by simpa [Fin.ext_iff]) (by simpa [Fin.ext_iff]) a b).map _

private theorem directLimitGen_rel {i j k : ℕ} (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (a b : R) :
    ⁅directLimitGen hij a, directLimitGen hjk b⁆ = directLimitGen hik (a * b) := by
  set m := max (max i j) k + 1
  rw [directLimitGen_eq_of hij a (m := m) (by omega) (by omega),
    directLimitGen_eq_of hjk b (m := m) (by omega) (by omega),
    directLimitGen_eq_of hik (a * b) (m := m) (by omega) (by omega),
    ← map_commutatorElement, commutatorElement_of]

variable (R) in
/-- The **direct-limit identification** of the stable Steinberg group: `SteinbergGroup ℕ R` is
canonically isomorphic to `DirectLimit (SteinbergGroup (Fin ·) R)` along stabilization. -/
def directLimitEquiv :
    DirectLimit (fun n : ℕ => SteinbergGroup (Fin n) R) (fun _ _ h => stabilize R h) ≃*
      SteinbergGroup ℕ R :=
  let fwd : DirectLimit (fun n : ℕ => SteinbergGroup (Fin n) R) (fun _ _ h => stabilize R h) →*
      SteinbergGroup ℕ R :=
    DirectLimit.Monoid.lift _ (fun _ _ h => stabilize R h) (fun n => ofFin R n)
      (fun _ _ h x => ofFin_stabilize h x)
  let bwd : SteinbergGroup ℕ R →*
      DirectLimit (fun n : ℕ => SteinbergGroup (Fin n) R) (fun _ _ h => stabilize R h) :=
    lift (fun hij a => directLimitGen hij a)
      (fun hij a b => directLimitGen_add hij a b)
      (fun hij hkl hjk hil a b => directLimitGen_comm hij hkl hjk hil a b)
      (fun hij hjk hik a b => directLimitGen_rel hij hjk hik a b)
  fwd.toMulEquiv bwd
    (DirectLimit.Monoid.hom_ext fun n => by
      refine hom_ext fun {i j} hij a => ?_
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      dsimp only [fwd]
      rw [DirectLimit.Monoid.lift_of, ofFin_of]
      have hbwd : bwd (of (Fin.val_injective.ne hij) a) =
          directLimitGen (Fin.val_injective.ne hij) a :=
        lift_of _ (fun hij a b => directLimitGen_add hij a b)
          (fun hij hkl hjk hil a b => directLimitGen_comm hij hkl hjk hil a b)
          (fun hij hjk hik a b => directLimitGen_rel hij hjk hik a b) _ a
      rw [hbwd, directLimitGen_eq_of _ a i.isLt j.isLt])
    (hom_ext fun hij a => by
      simp only [MonoidHom.comp_apply, MonoidHom.id_apply]
      have hbwd : bwd (of hij a) = directLimitGen hij a :=
        lift_of _ (fun hij a b => directLimitGen_add hij a b)
          (fun hij hkl hjk hil a b => directLimitGen_comm hij hkl hjk hil a b)
          (fun hij hjk hik a b => directLimitGen_rel hij hjk hik a b) hij a
      rw [hbwd, directLimitGen]
      dsimp only [fwd]
      rw [DirectLimit.Monoid.lift_of, ofFin_of])

/-- `directLimitEquiv` sends the image of `w : St_n(R)` in the direct limit to `ofFin R n w`. -/
theorem directLimitEquiv_of (n : ℕ) (w : SteinbergGroup (Fin n) R) :
    directLimitEquiv R
      (DirectLimit.Monoid.of (fun k : ℕ => SteinbergGroup (Fin k) R)
        (fun _ _ h => stabilize R h) n w) = ofFin R n w :=
  DirectLimit.Monoid.lift_of (fun k => ofFin R k) (fun _ _ h x => ofFin_stabilize h x) n w

/-- `directLimitEquiv` evaluates on a quotient representative `⟦⟨n, w⟩⟧` to `ofFin R n w`. -/
@[simp]
theorem directLimitEquiv_mk (n : ℕ) (w : SteinbergGroup (Fin n) R) :
    directLimitEquiv R (⟦⟨n, w⟩⟧ : DirectLimit (fun k : ℕ => SteinbergGroup (Fin k) R)
      (fun _ _ h => stabilize R h)) = ofFin R n w := by
  rw [← DirectLimit.Monoid.of_apply (G := fun k : ℕ => SteinbergGroup (Fin k) R)
    (f := fun _ _ h => stabilize R h) n w]
  exact directLimitEquiv_of n w

/-- `(directLimitEquiv R).symm` sends `ofFin R n w` to the image of `w` in the direct limit. -/
@[simp]
theorem directLimitEquiv_symm_ofFin (n : ℕ) (w : SteinbergGroup (Fin n) R) :
    (directLimitEquiv R).symm (ofFin R n w) =
      DirectLimit.Monoid.of (fun k : ℕ => SteinbergGroup (Fin k) R)
        (fun _ _ h => stabilize R h) n w := by
  rw [← directLimitEquiv_of n w, MulEquiv.symm_apply_apply]

/-- Every element of `SteinbergGroup ℕ R` comes from some finite-rank Steinberg group `St_n(R)`. -/
theorem exists_ofFin (x : SteinbergGroup ℕ R) :
    ∃ n, ∃ w : SteinbergGroup (Fin n) R, ofFin R n w = x := by
  obtain ⟨n, w, hw⟩ :=
    DirectLimit.exists_eq_mk (fun _ _ h => stabilize R h) ((directLimitEquiv R).symm x)
  refine ⟨n, w, ?_⟩
  rw [← directLimitEquiv_of n w, DirectLimit.Monoid.of_apply, ← hw, MulEquiv.apply_symm_apply]

/-- Any two elements of `SteinbergGroup ℕ R` come from a common finite-rank Steinberg group
`St_n(R)`. -/
theorem exists_ofFin₂ (x y : SteinbergGroup ℕ R) :
    ∃ n, ∃ u v : SteinbergGroup (Fin n) R, ofFin R n u = x ∧ ofFin R n v = y := by
  obtain ⟨n, u, v, hu, hv⟩ := DirectLimit.exists_eq_mk₂ (fun _ _ h => stabilize R h)
    ((directLimitEquiv R).symm x) ((directLimitEquiv R).symm y)
  refine ⟨n, u, v, ?_, ?_⟩
  · rw [← directLimitEquiv_of n u, DirectLimit.Monoid.of_apply, ← hu, MulEquiv.apply_symm_apply]
  · rw [← directLimitEquiv_of n v, DirectLimit.Monoid.of_apply, ← hv, MulEquiv.apply_symm_apply]

/-! ## The canonical homomorphism `St(R) →* GL_∞(R)` -/

variable (R) in
/-- The canonical homomorphism `toStableGL R : SteinbergGroup ℕ R →* StableGeneralLinearGroup R`
induced by the finite-rank homomorphisms `toGL (Fin n) R : St_n(R) →* GL (Fin n) R`. -/
def toStableGL : SteinbergGroup ℕ R →* StableGeneralLinearGroup R :=
  (DirectLimit.Monoid.lift (fun n : ℕ => SteinbergGroup (Fin n) R) (fun _ _ h => stabilize R h)
    (fun n => (StableGeneralLinearGroup.of R n).comp (toGL (Fin n) R))
    (fun _ _ h x => by
      simp only [MonoidHom.comp_apply, toGL_stabilize,
        StableGeneralLinearGroup.of_stabilizeGL])).comp
    (directLimitEquiv R).symm.toMonoidHom

/-- `toStableGL` agrees with `StableGeneralLinearGroup.of R n ∘ toGL (Fin n) R` on `ofFin R n`. -/
@[simp]
theorem toStableGL_ofFin (n : ℕ) (w : SteinbergGroup (Fin n) R) :
    toStableGL R (ofFin R n w) = StableGeneralLinearGroup.of R n (toGL (Fin n) R w) := by
  simp only [toStableGL, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    directLimitEquiv_symm_ofFin, DirectLimit.Monoid.lift_of]

/-- Composition form of `toStableGL_ofFin`. -/
theorem toStableGL_comp_ofFin (n : ℕ) :
    (toStableGL R).comp (ofFin R n) = (StableGeneralLinearGroup.of R n).comp (toGL (Fin n) R) :=
  MonoidHom.ext (toStableGL_ofFin n)

/-- On a root generator `xᵢⱼ(a)`, `toStableGL` yields the elementary matrix `eᵢⱼ(a)` at any size
`n` strictly exceeding `i` and `j`. -/
theorem toStableGL_of {i j : ℕ} (hij : i ≠ j) (a : R) {n : ℕ} (hi : i < n) (hj : j < n) :
    toStableGL R (of hij a) =
      StableGeneralLinearGroup.of R n
        (transvectionUnit (i := (⟨i, hi⟩ : Fin n)) (j := ⟨j, hj⟩) (by simpa [Fin.ext_iff]) a) := by
  have hgen : of hij a =
      ofFin R n (of (i := (⟨i, hi⟩ : Fin n)) (j := ⟨j, hj⟩) (by simpa [Fin.ext_iff]) a) := by
    rw [ofFin_of]
  rw [hgen, toStableGL_ofFin, toGL_of]

/-- The image of `toStableGL R : St(R) →* GL_∞(R)` is the stable elementary subgroup `E_∞(R)`. -/
theorem range_toStableGL :
    (toStableGL R).range = StableGeneralLinearGroup.elementarySubgroup R := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨x, rfl⟩
    obtain ⟨n, w, rfl⟩ := exists_ofFin x
    rw [toStableGL_ofFin]
    exact StableGeneralLinearGroup.of_mem_elementarySubgroup
      (range_toGL (ι := Fin n) (R := R) ▸ ⟨w, rfl⟩)
  · intro g hg
    obtain ⟨n, u, hu, rfl⟩ := StableGeneralLinearGroup.mem_elementarySubgroup_iff.mp hg
    rw [← range_toGL] at hu
    obtain ⟨w, rfl⟩ := hu
    exact ⟨ofFin R n w, toStableGL_ofFin n w⟩

/-- The column root subgroup `colHom R t` remains injective after mapping into the stable Steinberg
group `SteinbergGroup ℕ R`. -/
theorem ofFin_comp_colHom_injective (n : ℕ) (t : Fin n) :
    Function.Injective ((ofFin R n).comp (colHom R t)) := by
  refine Function.Injective.of_comp (f := toStableGL R) ?_
  have heq : (toStableGL R ∘ ((ofFin R n).comp (colHom R t))) =
      StableGeneralLinearGroup.of R n ∘ ((toGL (Fin n) R).comp (colHom R t)) := by
    funext v
    simp
  rw [heq]
  exact (StableGeneralLinearGroup.of_injective n).comp (toGL_comp_colHom_injective t)

/-- The row root subgroup `rowHom R t` remains injective after mapping into the stable Steinberg
group `SteinbergGroup ℕ R`. -/
theorem ofFin_comp_rowHom_injective (n : ℕ) (t : Fin n) :
    Function.Injective ((ofFin R n).comp (rowHom R t)) := by
  refine Function.Injective.of_comp (f := toStableGL R) ?_
  have heq : (toStableGL R ∘ ((ofFin R n).comp (rowHom R t))) =
      StableGeneralLinearGroup.of R n ∘ ((toGL (Fin n) R).comp (rowHom R t)) := by
    funext v
    simp
  rw [heq]
  exact (StableGeneralLinearGroup.of_injective n).comp (toGL_comp_rowHom_injective t)

/-- Ring homomorphisms preserve the kernel of `toStableGL`. -/
theorem map_mem_ker_toStableGL {S : Type*} [Ring S] (f : R →+* S) {x : SteinbergGroup ℕ R}
    (hx : x ∈ (toStableGL R).ker) : map f x ∈ (toStableGL S).ker := by
  obtain ⟨n, w, rfl⟩ := exists_ofFin x
  rw [MonoidHom.mem_ker, toStableGL_ofFin, ← map_one (StableGeneralLinearGroup.of R n)] at hx
  have hw : toGL (Fin n) R w = 1 := StableGeneralLinearGroup.of_injective n hx
  rw [MonoidHom.mem_ker, ← ofFin_map, toStableGL_ofFin, toGL_map, hw, map_one, map_one]

/-! ## The center of `SteinbergGroup ℕ R` and conditional finite-rank centrality -/

/-- **Centrality of the stable Steinberg kernel** (Milnor Theorem 5.1 / Weibel Theorem III.5.2.1):
every element of `ker (toStableGL R)` lies in the center of `SteinbergGroup ℕ R`. -/
theorem ker_toStableGL_le_center :
    (toStableGL R).ker ≤ Subgroup.center (SteinbergGroup ℕ R) := by
  intro z hz
  refine Subgroup.mem_center_iff.mpr fun y => ?_
  obtain ⟨n, u, v, rfl, rfl⟩ := exists_ofFin₂ z y
  rw [MonoidHom.mem_ker, toStableGL_ofFin, ← map_one (StableGeneralLinearGroup.of R n)] at hz
  have hu : toGL (Fin n) R u = 1 := StableGeneralLinearGroup.of_injective n hz
  have hcent : stabilize R (Nat.le_succ n) u ∈ Subgroup.center (SteinbergGroup (Fin (n + 1)) R) :=
    stabilize_mem_center_of_mem_ker_toGL (Nat.lt_succ_self n) hu
  have hcomm := Subgroup.mem_center_iff.mp hcent (stabilize R (Nat.le_succ n) v)
  have hap := congrArg (ofFin R (n + 1)) hcomm
  simpa only [map_mul, ofFin_stabilize] using hap

/-- Every central element of `SteinbergGroup ℕ R` lies in `ker (toStableGL R)`. -/
theorem center_le_ker_toStableGL :
    Subgroup.center (SteinbergGroup ℕ R) ≤ (toStableGL R).ker := by
  intro z hz
  obtain ⟨n, w, rfl⟩ := exists_ofFin z
  rw [MonoidHom.mem_ker, toStableGL_ofFin]
  suffices hgl : toGL (Fin n) R w = 1 by rw [hgl, map_one]
  set g : GL (Fin n) R := toGL (Fin n) R w
  ext k i
  have hcomm : ofFin R n w * of (ne_of_lt i.isLt) (1 : R) =
      of (ne_of_lt i.isLt) (1 : R) * ofFin R n w :=
    (Subgroup.mem_center_iff.mp hz _).symm
  have hmap := congrArg (toStableGL R) hcomm
  rw [map_mul, map_mul, toStableGL_ofFin,
    ← StableGeneralLinearGroup.of_stabilizeGL (Nat.le_succ n) g,
    toStableGL_of (ne_of_lt i.isLt) (1 : R) (n := n + 1) (Nat.lt_succ_of_lt i.isLt)
      (Nat.lt_succ_self n),
    ← map_mul, ← map_mul] at hmap
  have hgl_comm := StableGeneralLinearGroup.of_injective (n + 1) hmap
  have hmat := congrArg Units.val hgl_comm
  simp only [Units.val_mul, coe_transvectionUnit_eq_one_add_single, mul_add, add_mul, mul_one,
    one_mul] at hmat
  have hsingle := add_left_cancel hmat
  have hentry := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) R =>
    M k.castSucc (Fin.last n)) hsingle
  simp only [Matrix.mul_apply, Matrix.single_apply] at hentry
  have hlhs : (∑ x : Fin (n + 1),
      (stabilizeGL R (Nat.le_succ n) g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) k.castSucc x *
        if ⟨i.1, Nat.lt_succ_of_lt i.isLt⟩ = x ∧ ⟨n, Nat.lt_succ_self n⟩ = Fin.last n then (1 : R)
        else 0) = (g : Matrix (Fin n) (Fin n) R) k i := by
    rw [Finset.sum_eq_single (⟨i.1, Nat.lt_succ_of_lt i.isLt⟩ : Fin (n + 1))]
    · simp [coe_stabilizeGL_apply, k.isLt, i.isLt, Fin.last]
    · intro x _ hx
      simp [hx.symm]
    · intro hi_mem
      exact absurd (Finset.mem_univ _) hi_mem
  have hrhs : (∑ x : Fin (n + 1),
      (if ⟨i.1, Nat.lt_succ_of_lt i.isLt⟩ = k.castSucc ∧ ⟨n, Nat.lt_succ_self n⟩ = x then (1 : R)
        else 0) *
        (stabilizeGL R (Nat.le_succ n) g : Matrix (Fin (n + 1)) (Fin (n + 1)) R) x (Fin.last n)) =
      (1 : Matrix (Fin n) (Fin n) R) k i := by
    rw [Finset.sum_eq_single (Fin.last n)]
    · simp [Fin.last, coe_stabilizeGL_apply, Matrix.one_apply, Fin.ext_iff, eq_comm]
    · intro x _ hx
      have hne : (⟨n, Nat.lt_succ_self n⟩ : Fin (n + 1)) ≠ x := fun h => hx h.symm
      simp [hne]
    · intro hn_mem
      exact absurd (Finset.mem_univ _) hn_mem
  rw [hlhs, hrhs] at hentry
  simpa using hentry

/-- The kernel of `toStableGL R : St(R) →* GL_∞(R)` equals the entire center of
`SteinbergGroup ℕ R`. -/
theorem ker_toStableGL_eq_center :
    (toStableGL R).ker = Subgroup.center (SteinbergGroup ℕ R) :=
  le_antisymm ker_toStableGL_le_center center_le_ker_toStableGL

/-- **Conditional finite-rank centrality**: if the stabilization inclusion
`ofFin R n : St_n(R) →* St(R)` is injective on `ker (toGL (Fin n) R)`, then
`ker (toGL (Fin n) R)` is central in `SteinbergGroup (Fin n) R`. -/
theorem ker_toGL_le_center_of_injOn_ofFin {n : ℕ}
    (hinj : Set.InjOn (ofFin R n) (toGL (Fin n) R).ker) :
    (toGL (Fin n) R).ker ≤ Subgroup.center (SteinbergGroup (Fin n) R) := by
  intro x hx
  refine Subgroup.mem_center_iff.mpr fun y => ?_
  have hcomm_ker : ⁅y, x⁆ ∈ (toGL (Fin n) R).ker := by
    rw [MonoidHom.mem_ker, map_commutatorElement, MonoidHom.mem_ker.mp hx,
      commutatorElement_one_right]
  have hx_stable : ofFin R n x ∈ (toStableGL R).ker := by
    rw [MonoidHom.mem_ker, toStableGL_ofFin, MonoidHom.mem_ker.mp hx, map_one]
  have hof_comm : ofFin R n ⁅y, x⁆ = ofFin R n 1 := by
    rw [map_commutatorElement, map_one, commutatorElement_eq_one_iff_commute]
    exact (Subgroup.mem_center_iff.mp (ker_toStableGL_le_center hx_stable) (ofFin R n y))
  have htriv : ⁅y, x⁆ = 1 := hinj hcomm_ker (one_mem _) hof_comm
  exact commutatorElement_eq_one_iff_commute.mp htriv

/-! ## The Kervaire–Steinberg universal central extension -/

variable (R) in
/-- The canonical surjection `St(R) →* E_∞(R)` obtained by corestricting `toStableGL R` to the
stable elementary subgroup. -/
def toStableElementary : SteinbergGroup ℕ R →* StableGeneralLinearGroup.elementarySubgroup R :=
  (toStableGL R).codRestrict (StableGeneralLinearGroup.elementarySubgroup R) fun x =>
    range_toStableGL (R := R) ▸ ⟨x, rfl⟩

/-- The underlying element of `GL_∞(R)` for `toStableElementary R x` is `toStableGL R x`. -/
@[simp]
theorem coe_toStableElementary (x : SteinbergGroup ℕ R) :
    (toStableElementary R x : StableGeneralLinearGroup R) = toStableGL R x :=
  (rfl)

/-- `toStableElementary R : St(R) →* E_∞(R)` is surjective. -/
theorem toStableElementary_surjective : Function.Surjective (toStableElementary R) := by
  rintro ⟨g, hg⟩
  rw [← range_toStableGL] at hg
  obtain ⟨x, rfl⟩ := hg
  exact ⟨x, rfl⟩

/-- The kernel of `toStableElementary R` equals the kernel of `toStableGL R`. -/
theorem ker_toStableElementary : (toStableElementary R).ker = (toStableGL R).ker := by
  ext x
  simp [Subtype.ext_iff]

/-- `toStableElementary R : St(R) →* E_∞(R)` is a central extension. -/
theorem isCentralExtension_toStableElementary :
    (toStableElementary R).IsCentralExtension where
  surjective := toStableElementary_surjective
  ker_le_center := (ker_toStableElementary (R := R)).symm ▸ ker_toStableGL_le_center

/-- **Kervaire–Steinberg theorem**: for every associative unital ring `R`, the canonical surjection
`toStableElementary R : St(R) →* E_∞(R)` is a universal central extension of the stable elementary
group `E_∞(R)`. -/
theorem isUniversalCentralExtension_toStableElementary.{v} :
    (toStableElementary R).IsUniversalCentralExtension.{v} where
  isCentralExtension := isCentralExtension_toStableElementary
  existsUnique_comp_eq _ _ _ hq :=
    existsUnique_lift_of_ker_le_center (toStableElementary R) _
      (by rw [MonoidHom.range_eq_top.mpr hq.surjective]; exact le_top)
      hq.ker_le_center (by simp)

/-- Direct `GL_∞(R)` formulation of the Kervaire–Steinberg universal central extension: for any
group `E` (in any universe) and any homomorphism `q : E →* GL_∞(R)` whose image is `E_∞(R)` and
whose kernel is central in `E`, there is a unique homomorphism `ψ : St(R) →* E` with
`q.comp ψ = toStableGL R`. -/
theorem existsUnique_lift_toStableGL {E : Type*} [Group E]
    (q : E →* StableGeneralLinearGroup R)
    (hrange : q.range = StableGeneralLinearGroup.elementarySubgroup R)
    (hker : q.ker ≤ Subgroup.center E) :
    ∃! ψ : SteinbergGroup ℕ R →* E, q.comp ψ = toStableGL R :=
  existsUnique_lift_of_ker_le_center (toStableGL R) q
    (by rw [range_toStableGL, hrange]) hker (by simp)

end SteinbergGroup

end TauCeti
