/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.UniversalCentralExtension
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Basic
import Mathlib.GroupTheory.NoncommPiCoprod
import TauCeti.GroupTheory.Commutator

/-!
# The Steinberg group as the universal central extension of `E(R)`

For an associative unital ring `R`, the Steinberg generators `x_{ij}(a)` map to the elementary
transvections `e_{ij}(a) = 1 + a E_{ij}` in the stable general linear group `GL_∞(R)`, defining a
group homomorphism `TauCeti.SteinbergGroup.toStableGL : St(R) →* GL_∞(R)` whose image is the stable
elementary subgroup `E_∞(R)`.

This file proves the **Kervaire–Steinberg theorem**:

1. **Centrality of the kernel (`K₂(R) ≤ Z(St(R))`).** Every element `z ∈ ker(St(R) →* GL_∞(R))`
   comes from `Stₙ(R)` for some `n`. The subgroup `Stₙ(R)` normalizes both the `n`-th column root
   subgroup `Pₙ = ⟨x_{in}(a) | i < n⟩` and the `n`-th row root subgroup
   `Qₙ = ⟨x_{nj}(b) | j < n⟩`, on each of which `toStableGL` is injective via upper and lower block
   unipotent matrices in `GL_{n + 1}(R)`. Hence `z` centralizes `Pₙ` and `Qₙ`, and therefore every
   generator `x_{pq}(b) = ⁅x_{pn}(b), x_{nq}(1)⁆` with `p, q < n`.
2. **Universal central extension.** Given any group `E` (in an arbitrary universe) and homomorphism
   `q : E →* GL_∞(R)` with image `E_∞(R)` and central kernel, commutators `⁅u, v⁆` in `E` depend
   only on `q(u)` and `q(v)`. Defining `ψ(x_{ij}(a)) = ⁅u_{im}(a), u_{mj}(1)⁆` for `m = max i j + 1`
   and chosen lifts `u` in `E`, a four-index commutator associativity `⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆`
   for lifted transvections shows independence of the auxiliary index `m` and establishes all three
   Steinberg relations in `E`. Since `St(R)` is perfect, the resulting lift `ψ : St(R) →* E`
   satisfying `q ∘ ψ = toStableGL R` is unique.

## Main definitions

* `TauCeti.SteinbergGroup.toStableGL`: the canonical homomorphism `St(R) →* GL_∞(R)`.
* `TauCeti.SteinbergGroup.toElementarySubgroup`: the surjective homomorphism `St(R) →* E_∞(R)`.
* `TauCeti.SteinbergGroup.liftCentralExtension`: the unique lift `St(R) →* E` into any central
  extension `q : E →* GL_∞(R)` of `E_∞(R)`.

## Main results

* `TauCeti.SteinbergGroup.range_toStableGL`: the image of `toStableGL R` is
  `TauCeti.StableGeneralLinearGroup.elementarySubgroup R`.
* `TauCeti.SteinbergGroup.ker_toStableGL_le_center`: `ker (toStableGL R)` lies in the center of
  `St(R)`.
* `TauCeti.SteinbergGroup.existsUnique_comp_eq_toStableGL`: existence and uniqueness of lifts from
  `St(R)` into central extensions of `E_∞(R)`.
* `TauCeti.SteinbergGroup.isUniversalCentralExtension_toElementarySubgroup`:
  `toElementarySubgroup R` satisfies `MonoidHom.IsUniversalCentralExtension`.
* `TauCeti.steinberg_universalCentralExtension`: the packaged Kervaire–Steinberg universal central
  extension theorem over `GL_∞(R)`.

## References

* R. Steinberg, *Générateurs, relations et revêtements de groupes algébriques*, in *Colloq.
  Théorie des Groupes Algébriques (Bruxelles, 1962)*, Librairie Universitaire, Louvain;
  Gauthier-Villars, Paris (1962), 113–127.
* M. Kervaire, *Multiplicateurs de Schur et K-théorie*, in *Essays on Topology and Related
  Topics* (Mémoires dédiés à Georges de Rham), Springer (1970), 212–225.
* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5,
  Theorems 5.1 and 5.10.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Theorem 5.2.1, Lemma 5.3.3, and Theorem 5.5.
-/

public section

noncomputable section

open Matrix Subgroup

open scoped commutatorElement

namespace TauCeti

universe u v

namespace SteinbergGroup

/-! ## The canonical homomorphism `St(R) →* GL_∞(R)` -/

section ToStableGL

variable (R : Type u) [Ring R]

/-- The canonical homomorphism `St(R) →* GL_∞(R)` sending each generator `x_{ij}(a)` to
`TauCeti.stableTransvection ⟨(i, j), hij⟩ a`. -/
def toStableGL : SteinbergGroup R →* StableGeneralLinearGroup R :=
  IndexedSteinbergGroup.lift
    (fun i j hij a ↦ stableTransvection ⟨(i, j), hij⟩ a)
    (fun i j hij a b ↦ stableTransvection_add ⟨(i, j), hij⟩ a b)
    (fun _ _ _ _ hij hkl hjk hli a b ↦ commute_stableTransvection hij hkl hjk hli a b)
    (fun _ _ _ hij hjk hik a b ↦ commutatorElement_stableTransvection hij hjk hik a b)

variable {R}

@[simp]
theorem toStableGL_x {i j : ℕ} (hij : i ≠ j) (a : R) :
    toStableGL R (IndexedSteinbergGroup.x hij a) = stableTransvection ⟨(i, j), hij⟩ a :=
  IndexedSteinbergGroup.lift_x _ _ _ _ hij a

@[simp]
theorem toStableGL_of (p : {p : ℕ × ℕ // p.1 ≠ p.2}) (a : R) :
    toStableGL R (PresentedGroup.of (p, a)) = stableTransvection p a := by
  rw [IndexedSteinbergGroup.of_eq_x, toStableGL_x]

/-- On the image of `Stₙ(R)`, `toStableGL R` agrees with `IndexedSteinbergGroup.toGL` followed by
`StableGeneralLinearGroup.of R n`. -/
@[simp]
theorem toStableGL_ofFin (n : ℕ) (u : IndexedSteinbergGroup (Fin n) R) :
    toStableGL R (ofFin R n u) =
      StableGeneralLinearGroup.of R n (IndexedSteinbergGroup.toGL u) := by
  have hhom : (toStableGL R).comp (ofFin R n) =
      (StableGeneralLinearGroup.of R n).comp IndexedSteinbergGroup.toGL := by
    ext i j hij a
    simp only [MonoidHom.comp_apply, ofFin_x, toStableGL_x, IndexedSteinbergGroup.toGL_x]
    exact stableTransvection_eq_of ⟨(i.1, j.1), Fin.val_ne_of_ne hij⟩ a i.2 j.2
  exact DFunLike.congr_fun hhom u

/-- The image of `toStableGL R` in `GL_∞(R)` is the stable elementary subgroup `E_∞(R)`. -/
theorem range_toStableGL :
    (toStableGL R).range = StableGeneralLinearGroup.elementarySubgroup R := by
  refine le_antisymm ?_ fun y hy ↦ ?_
  · refine IndexedSteinbergGroup.range_le_iff.mpr fun i j hij a ↦ ?_
    rw [toStableGL_x]
    exact stableTransvection_mem_elementarySubgroup ⟨(i, j), hij⟩ a
  · obtain ⟨n, u, hu, rfl⟩ := StableGeneralLinearGroup.mem_elementarySubgroup_iff.mp hy
    rw [← IndexedSteinbergGroup.range_toGL] at hu
    obtain ⟨z, rfl⟩ := hu
    exact ⟨ofFin R n z, toStableGL_ofFin n z⟩

variable (R) in
/-- The canonical projection `St(R) →* E_∞(R)` onto the stable elementary subgroup. -/
def toElementarySubgroup :
    SteinbergGroup R →* StableGeneralLinearGroup.elementarySubgroup R :=
  (toStableGL R).codRestrict (StableGeneralLinearGroup.elementarySubgroup R) fun z ↦
    range_toStableGL (R := R) ▸ ⟨z, rfl⟩

@[simp]
theorem coe_toElementarySubgroup (z : SteinbergGroup R) :
    (toElementarySubgroup R z : StableGeneralLinearGroup R) = toStableGL R z :=
  (rfl)

/-- The canonical projection `St(R) →* E_∞(R)` is surjective. -/
theorem toElementarySubgroup_surjective :
    Function.Surjective (toElementarySubgroup R) := by
  rintro ⟨y, hy⟩
  rw [← range_toStableGL] at hy
  obtain ⟨z, rfl⟩ := hy
  exact ⟨z, rfl⟩

@[simp]
theorem ker_toElementarySubgroup :
    (toElementarySubgroup R).ker = (toStableGL R).ker := by
  ext z
  simp [MonoidHom.mem_ker, Subtype.ext_iff]

end ToStableGL

/-! ## Centrality of `ker (toStableGL R)` -/

section Center

variable {R : Type u} [Ring R]

private theorem toStableGL_comp_ofFin_comp_injective {H : Type*} [Group H] {m : ℕ}
    {φ : H →* IndexedSteinbergGroup (Fin m) R} {ψ : H →* GL (Fin m) R}
    (hcomp : (IndexedSteinbergGroup.toGL (R := R)).comp φ = ψ)
    (hinj : Function.Injective ψ) :
    Function.Injective ((toStableGL R).comp ((ofFin R m).comp φ)) := by
  have h : (toStableGL R).comp ((ofFin R m).comp φ) =
      (StableGeneralLinearGroup.of R m).comp ψ := by
    ext f
    simpa only [MonoidHom.comp_apply, toStableGL_ofFin] using
      congrArg (StableGeneralLinearGroup.of R m) (DFunLike.congr_fun hcomp f)
  rw [h]
  exact (StableGeneralLinearGroup.of_injective m).comp hinj

private theorem range_ofFin_le_normalizer_of_map_conj_le {n : ℕ}
    {U : Subgroup (SteinbergGroup R)}
    (hconj : ∀ {i j : Fin n} (hij : i ≠ j) (c : R),
      U.map (MulAut.conj (ofFin R n (IndexedSteinbergGroup.x hij c))) ≤ U) :
    (ofFin R n).range ≤ Subgroup.normalizer (U : Set (SteinbergGroup R)) := by
  rw [IndexedSteinbergGroup.range_le_iff]
  intro i j hij c
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm (hconj hij c) fun y hy ↦ ?_
  refine ⟨(ofFin R n (IndexedSteinbergGroup.x hij c))⁻¹ * y *
    ofFin R n (IndexedSteinbergGroup.x hij c), ?_,
    by rw [MonoidHom.coe_ofClass, MulAut.conj_apply]; group⟩
  have hinv : (ofFin R n (IndexedSteinbergGroup.x hij c))⁻¹ =
      ofFin R n (IndexedSteinbergGroup.x hij (-c)) := by
    rw [← map_inv, IndexedSteinbergGroup.x_inv]
  have hmem : MulAut.conj (ofFin R n (IndexedSteinbergGroup.x hij (-c))) y ∈ U :=
    hconj hij (-c) ⟨y, hy, rfl⟩
  simpa only [SetLike.mem_coe, MulAut.conj_apply, ← hinv, inv_inv] using hmem

private theorem colHomFin_pairwise (n : ℕ) :
    Pairwise fun i j : Fin n ↦ ∀ a b : Multiplicative R,
      Commute (IndexedSteinbergGroup.xHom (Fin.castSucc_lt_last i).ne a)
        (IndexedSteinbergGroup.xHom (Fin.castSucc_lt_last j).ne b) := by
  intro i j _ a b
  simp only [IndexedSteinbergGroup.xHom_apply]
  exact IndexedSteinbergGroup.commute_x
    (Fin.castSucc_lt_last i).ne (Fin.castSucc_lt_last j).ne
    (Fin.castSucc_lt_last j).ne.symm (Fin.castSucc_lt_last i).ne.symm a.toAdd b.toAdd

/-- The homomorphism `(Fin n → Multiplicative R) →* St_{n + 1}(R)` assembling the commuting column
root subgroups `x_{i, n}` (`i < n`). -/
private def colHomFin (n : ℕ) :
    (Fin n → Multiplicative R) →* IndexedSteinbergGroup (Fin (n + 1)) R :=
  MonoidHom.noncommPiCoprod
    (fun i : Fin n ↦ IndexedSteinbergGroup.xHom (Fin.castSucc_lt_last i).ne)
    (colHomFin_pairwise n)

/-- The homomorphism `(Fin n → Multiplicative R) →* St(R)` assembling the commuting column root
subgroups `x_{i, n}` (`i < n`). -/
private def colHom (n : ℕ) : (Fin n → Multiplicative R) →* SteinbergGroup R :=
  (ofFin R (n + 1)).comp (colHomFin n)

/-- The upper block unipotent homomorphism `(Fin n → Multiplicative R) →* GL (Fin (n + 1)) R`
placing a column vector in the last column. -/
private def upperColGLHom (n : ℕ) :
    (Fin n → Multiplicative R) →* GL (Fin (n + 1)) R where
  toFun f := (finSumFinEquiv (m := n) (n := 1)).reindexGL R
    (Matrix.upperBlockGL (Matrix.of fun i (_ : Fin 1) ↦ (f i).toAdd))
  map_one' := by
    have h0 : (Matrix.of fun (i : Fin n) (_ : Fin 1) ↦
        (((1 : Fin n → Multiplicative R) i).toAdd : R)) = 0 := by
      ext
      simp only [Pi.one_apply, toAdd_one, Matrix.of_apply, Matrix.zero_apply]
    rw [h0, Matrix.upperBlockGL_zero, map_one]
  map_mul' f g := by
    have hadd : (Matrix.of fun i (_ : Fin 1) ↦ ((f * g) i).toAdd) =
        (Matrix.of fun i (_ : Fin 1) ↦ (f i).toAdd) +
          (Matrix.of fun i (_ : Fin 1) ↦ (g i).toAdd) := by
      ext i _
      exact toAdd_mul (f i) (g i)
    rw [hadd, Matrix.upperBlockGL_add, map_mul]

private theorem upperColGLHom_injective (n : ℕ) :
    Function.Injective (upperColGLHom (R := R) n) := by
  intro f g hfg
  dsimp only [upperColGLHom, MonoidHom.coe_mk, OneHom.coe_mk] at hfg
  have hblk := ((finSumFinEquiv (m := n) (n := 1)).reindexGL R).injective hfg
  ext i
  have hentry := congrArg (fun u : GL (Fin n ⊕ Fin 1) R ↦
    (u : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R) (Sum.inl i) (Sum.inr 0)) hblk
  simpa [Matrix.coe_upperBlockGL] using hentry

private theorem toGL_comp_colHomFin (n : ℕ) :
    (IndexedSteinbergGroup.toGL (R := R)).comp (colHomFin n) = upperColGLHom n := by
  refine MonoidHom.pi_ext fun i a ↦ ?_
  rw [MonoidHom.comp_apply, colHomFin, MonoidHom.noncommPiCoprod_mulSingle,
    IndexedSteinbergGroup.xHom_apply, IndexedSteinbergGroup.toGL_x]
  dsimp only [upperColGLHom, MonoidHom.coe_mk, OneHom.coe_mk]
  have hblk : Matrix.upperBlockGL (Matrix.of fun k (_ : Fin 1) ↦
      ((Pi.mulSingle i a : Fin n → Multiplicative R) k).toAdd) =
      transvectionUnit (Sum.inl_ne_inr (a := i) (b := (0 : Fin 1))) a.toAdd := by
    ext (p | p) (q | q)
    · simp [coe_transvectionUnit_eq_one_add_single, Matrix.one_apply]
    · fin_cases q
      by_cases hpi : p = i
      · subst hpi
        simp [coe_transvectionUnit_eq_one_add_single]
      · simp [coe_transvectionUnit_eq_one_add_single, hpi, Ne.symm hpi]
    · simp [coe_transvectionUnit_eq_one_add_single]
    · simp [coe_transvectionUnit_eq_one_add_single, Matrix.one_apply]
  rw [hblk, Equiv.reindexGL_transvectionUnit]
  have hi_eq : finSumFinEquiv (m := n) (n := 1) (Sum.inl i) = i.castSucc := by ext; simp
  have hj_eq : finSumFinEquiv (m := n) (n := 1) (Sum.inr 0) = Fin.last n := by ext; simp
  simp only [hi_eq, hj_eq]

private theorem toStableGL_comp_colHom_injective (n : ℕ) :
    Function.Injective ((toStableGL R).comp (colHom n)) :=
  toStableGL_comp_ofFin_comp_injective (toGL_comp_colHomFin n) (upperColGLHom_injective n)

private theorem mem_range_colHom {n : ℕ} (i : Fin n) (a : R) :
    IndexedSteinbergGroup.x i.isLt.ne a ∈ (colHom (R := R) n).range := by
  refine ⟨Pi.mulSingle i (Multiplicative.ofAdd a), ?_⟩
  rw [colHom, MonoidHom.comp_apply, colHomFin, MonoidHom.noncommPiCoprod_mulSingle,
    IndexedSteinbergGroup.xHom_apply, ofFin_x]
  simp only [Fin.val_castSucc, Fin.val_last, toAdd_ofAdd]

private theorem conj_colHom_mem_range_colHom {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : R) :
    ((colHom (R := R) n).range).map
      (MulAut.conj (ofFin R n (IndexedSteinbergGroup.x hij c))) ≤
      (colHom (R := R) n).range := by
  have hrange : (colHom (R := R) n).range =
      ⨆ k : Fin n, ((ofFin R (n + 1)).comp
        (IndexedSteinbergGroup.xHom (Fin.castSucc_lt_last k).ne)).range := by
    rw [colHom, MonoidHom.range_comp, colHomFin, MonoidHom.noncommPiCoprod_range,
      Subgroup.map_iSup]
    simp_rw [← MonoidHom.range_comp]
  rw [hrange, Subgroup.map_iSup]
  refine iSup_le fun k ↦ ?_
  rintro _ ⟨_, ⟨a, rfl⟩, rfl⟩
  simp only [MonoidHom.comp_apply, IndexedSteinbergGroup.xHom_apply, ofFin_x,
    Fin.val_castSucc, Fin.val_last, MonoidHom.coe_ofClass, MulAut.conj_apply]
  by_cases hjk : j = k
  · subst hjk
    rw [IndexedSteinbergGroup.mul_x_mul_inv (Fin.val_ne_of_ne hij) j.isLt.ne i.isLt.ne]
    rw [← hrange]
    exact mul_mem (mem_range_colHom i (c * a.toAdd)) (mem_range_colHom j a.toAdd)
  · have hcomm := IndexedSteinbergGroup.commute_x
      (Fin.val_ne_of_ne hij) k.isLt.ne (Fin.val_ne_of_ne hjk) i.isLt.ne.symm c a.toAdd
    rw [hcomm.eq, mul_inv_cancel_right, ← hrange]
    exact mem_range_colHom k a.toAdd

private theorem range_ofFin_le_normalizer_colHom (n : ℕ) :
    (ofFin R n).range ≤
      Subgroup.normalizer ((colHom (R := R) n).range : Set (SteinbergGroup R)) :=
  range_ofFin_le_normalizer_of_map_conj_le conj_colHom_mem_range_colHom

private theorem rowHomFin_pairwise (n : ℕ) :
    Pairwise fun i j : Fin n ↦ ∀ a b : Multiplicative R,
      Commute (IndexedSteinbergGroup.xHom (Fin.castSucc_lt_last i).ne.symm a)
        (IndexedSteinbergGroup.xHom (Fin.castSucc_lt_last j).ne.symm b) := by
  intro i j _ a b
  simp only [IndexedSteinbergGroup.xHom_apply]
  exact IndexedSteinbergGroup.commute_x
    (Fin.castSucc_lt_last i).ne.symm (Fin.castSucc_lt_last j).ne.symm
    (Fin.castSucc_lt_last i).ne (Fin.castSucc_lt_last j).ne a.toAdd b.toAdd

/-- The homomorphism `(Fin n → Multiplicative R) →* St_{n + 1}(R)` assembling the commuting row
root subgroups `x_{n, j}` (`j < n`). -/
private def rowHomFin (n : ℕ) :
    (Fin n → Multiplicative R) →* IndexedSteinbergGroup (Fin (n + 1)) R :=
  MonoidHom.noncommPiCoprod
    (fun j : Fin n ↦ IndexedSteinbergGroup.xHom (Fin.castSucc_lt_last j).ne.symm)
    (rowHomFin_pairwise n)

/-- The homomorphism `(Fin n → Multiplicative R) →* St(R)` assembling the commuting row root
subgroups `x_{n, j}` (`j < n`). -/
private def rowHom (n : ℕ) : (Fin n → Multiplicative R) →* SteinbergGroup R :=
  (ofFin R (n + 1)).comp (rowHomFin n)

/-- The lower block unipotent homomorphism `(Fin n → Multiplicative R) →* GL (Fin (n + 1)) R`
placing a row vector in the last row. -/
private def lowerRowGLHom (n : ℕ) :
    (Fin n → Multiplicative R) →* GL (Fin (n + 1)) R where
  toFun f := (finSumFinEquiv (m := n) (n := 1)).reindexGL R
    (Matrix.lowerBlockGL (Matrix.of fun (_ : Fin 1) j ↦ (f j).toAdd))
  map_one' := by
    have h0 : (Matrix.of fun (_ : Fin 1) (j : Fin n) ↦
        (((1 : Fin n → Multiplicative R) j).toAdd : R)) = 0 := by
      ext
      simp only [Pi.one_apply, toAdd_one, Matrix.of_apply, Matrix.zero_apply]
    rw [h0, Matrix.lowerBlockGL_zero, map_one]
  map_mul' f g := by
    have hadd : (Matrix.of fun (_ : Fin 1) j ↦ ((f * g) j).toAdd) =
        (Matrix.of fun (_ : Fin 1) j ↦ (f j).toAdd) +
          (Matrix.of fun (_ : Fin 1) j ↦ (g j).toAdd) := by
      ext _ j
      exact toAdd_mul (f j) (g j)
    rw [hadd, Matrix.lowerBlockGL_add, map_mul]

private theorem lowerRowGLHom_injective (n : ℕ) :
    Function.Injective (lowerRowGLHom (R := R) n) := by
  intro f g hfg
  dsimp only [lowerRowGLHom, MonoidHom.coe_mk, OneHom.coe_mk] at hfg
  have hblk := ((finSumFinEquiv (m := n) (n := 1)).reindexGL R).injective hfg
  ext j
  have hentry := congrArg (fun u : GL (Fin n ⊕ Fin 1) R ↦
    (u : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) R) (Sum.inr 0) (Sum.inl j)) hblk
  simpa [Matrix.coe_lowerBlockGL] using hentry

private theorem toGL_comp_rowHomFin (n : ℕ) :
    (IndexedSteinbergGroup.toGL (R := R)).comp (rowHomFin n) = lowerRowGLHom n := by
  refine MonoidHom.pi_ext fun j a ↦ ?_
  rw [MonoidHom.comp_apply, rowHomFin, MonoidHom.noncommPiCoprod_mulSingle,
    IndexedSteinbergGroup.xHom_apply, IndexedSteinbergGroup.toGL_x]
  dsimp only [lowerRowGLHom, MonoidHom.coe_mk, OneHom.coe_mk]
  have hblk : Matrix.lowerBlockGL (Matrix.of fun (_ : Fin 1) k ↦
      ((Pi.mulSingle j a : Fin n → Multiplicative R) k).toAdd) =
      transvectionUnit (Sum.inr_ne_inl (a := j) (b := (0 : Fin 1))) a.toAdd := by
    ext (p | p) (q | q)
    · simp [coe_transvectionUnit_eq_one_add_single, Matrix.one_apply]
    · simp [coe_transvectionUnit_eq_one_add_single]
    · fin_cases p
      by_cases hqj : q = j
      · subst hqj
        simp [coe_transvectionUnit_eq_one_add_single]
      · simp [coe_transvectionUnit_eq_one_add_single, hqj, Ne.symm hqj]
    · simp [coe_transvectionUnit_eq_one_add_single, Matrix.one_apply]
  rw [hblk, Equiv.reindexGL_transvectionUnit]
  have hi_eq : finSumFinEquiv (m := n) (n := 1) (Sum.inr 0) = Fin.last n := by ext; simp
  have hj_eq : finSumFinEquiv (m := n) (n := 1) (Sum.inl j) = j.castSucc := by ext; simp
  simp only [hi_eq, hj_eq]

private theorem toStableGL_comp_rowHom_injective (n : ℕ) :
    Function.Injective ((toStableGL R).comp (rowHom n)) :=
  toStableGL_comp_ofFin_comp_injective (toGL_comp_rowHomFin n) (lowerRowGLHom_injective n)

private theorem mem_range_rowHom {n : ℕ} (j : Fin n) (b : R) :
    IndexedSteinbergGroup.x j.isLt.ne.symm b ∈ (rowHom (R := R) n).range := by
  refine ⟨Pi.mulSingle j (Multiplicative.ofAdd b), ?_⟩
  rw [rowHom, MonoidHom.comp_apply, rowHomFin, MonoidHom.noncommPiCoprod_mulSingle,
    IndexedSteinbergGroup.xHom_apply, ofFin_x]
  simp only [Fin.val_last, Fin.val_castSucc, toAdd_ofAdd]

private theorem conj_rowHom_mem_range_rowHom {n : ℕ} {i j : Fin n} (hij : i ≠ j) (c : R) :
    ((rowHom (R := R) n).range).map
      (MulAut.conj (ofFin R n (IndexedSteinbergGroup.x hij c))) ≤
      (rowHom (R := R) n).range := by
  have hrange : (rowHom (R := R) n).range =
      ⨆ l : Fin n, ((ofFin R (n + 1)).comp
        (IndexedSteinbergGroup.xHom (Fin.castSucc_lt_last l).ne.symm)).range := by
    rw [rowHom, MonoidHom.range_comp, rowHomFin, MonoidHom.noncommPiCoprod_range,
      Subgroup.map_iSup]
    simp_rw [← MonoidHom.range_comp]
  rw [hrange, Subgroup.map_iSup]
  refine iSup_le fun l ↦ ?_
  rintro _ ⟨_, ⟨b, rfl⟩, rfl⟩
  simp only [MonoidHom.comp_apply, IndexedSteinbergGroup.xHom_apply, ofFin_x,
    Fin.val_last, Fin.val_castSucc, MonoidHom.coe_ofClass, MulAut.conj_apply]
  by_cases hil : i = l
  · subst hil
    rw [IndexedSteinbergGroup.mul_x_mul_inv_reverse (Fin.val_ne_of_ne hij) i.isLt.ne.symm
      j.isLt.ne.symm]
    rw [← hrange]
    exact mul_mem (mem_range_rowHom j (-(b.toAdd * c))) (mem_range_rowHom i b.toAdd)
  · have hcomm := IndexedSteinbergGroup.commute_x
      (Fin.val_ne_of_ne hij) l.isLt.ne.symm j.isLt.ne (Fin.val_ne_of_ne hil).symm c b.toAdd
    rw [hcomm.eq, mul_inv_cancel_right, ← hrange]
    exact mem_range_rowHom l b.toAdd

private theorem range_ofFin_le_normalizer_rowHom (n : ℕ) :
    (ofFin R n).range ≤
      Subgroup.normalizer ((rowHom (R := R) n).range : Set (SteinbergGroup R)) :=
  range_ofFin_le_normalizer_of_map_conj_le conj_rowHom_mem_range_rowHom

/-- **Milnor's centrality theorem (`K₂(R) ≤ Z(St(R))`).** The kernel of `toStableGL R` lies in the
center of `SteinbergGroup R`. -/
theorem ker_toStableGL_le_center :
    (toStableGL R).ker ≤ Subgroup.center (SteinbergGroup R) := by
  intro z hz
  obtain ⟨m, u, rfl⟩ := exists_ofFin z
  have htop : Subgroup.centralizer {ofFin R m u} = ⊤ := by
    rw [IndexedSteinbergGroup.subgroup_eq_top_iff]
    intro p q hpq b
    let n := max m (max p q + 1)
    have hmn : m ≤ n := le_max_left _ _
    have hp : p < n := by omega
    have hq : q < n := by omega
    rw [Subgroup.mem_centralizer_iff]
    intro _ hw
    rw [Set.mem_singleton_iff.mp hw, ← ofFin_stabilize hmn u]
    have hzn_mem : ofFin R n (stabilize hmn u) ∈ (ofFin R n).range := ⟨stabilize hmn u, rfl⟩
    have hzn_ker : ofFin R n (stabilize hmn u) ∈ (toStableGL R).ker := by
      rwa [ofFin_stabilize hmn u]
    have hcp : Commute (ofFin R n (stabilize hmn u)) (IndexedSteinbergGroup.x hp.ne b) :=
      commute_of_mem_ker_of_mem_normalizer (toStableGL_comp_colHom_injective n) hzn_ker
        (range_ofFin_le_normalizer_colHom n hzn_mem) (mem_range_colHom ⟨p, hp⟩ b)
    have hcq : Commute (ofFin R n (stabilize hmn u)) (IndexedSteinbergGroup.x hq.ne.symm 1) :=
      commute_of_mem_ker_of_mem_normalizer (toStableGL_comp_rowHom_injective n) hzn_ker
        (range_ofFin_le_normalizer_rowHom n hzn_mem) (mem_range_rowHom ⟨q, hq⟩ 1)
    have hcomm : Commute (ofFin R n (stabilize hmn u))
        ⁅IndexedSteinbergGroup.x hp.ne b, IndexedSteinbergGroup.x hq.ne.symm 1⁆ := by
      rw [commutatorElement_def]
      exact ((hcp.mul_right hcq).mul_right hcp.inv_right).mul_right hcq.inv_right
    rwa [IndexedSteinbergGroup.commutatorElement_x hp.ne hq.ne.symm hpq, mul_one] at hcomm
  refine Subgroup.mem_center_iff.mpr fun w ↦ ?_
  have hw : w ∈ Subgroup.centralizer {ofFin R m u} := htop ▸ Subgroup.mem_top w
  exact (Subgroup.mem_centralizer_iff.mp hw (ofFin R m u) rfl).symm

/-- The canonical projection `St(R) →* E_∞(R)` is a central extension. -/
theorem isCentralExtension_toElementarySubgroup :
    (toElementarySubgroup R).IsCentralExtension where
  surjective := toElementarySubgroup_surjective
  ker_le_center := ker_toElementarySubgroup (R := R) ▸ ker_toStableGL_le_center

end Center

/-! ## Universal central extension property -/

section Universal

variable {R : Type u} [Ring R] {E : Type v} [Group E]

/-- Any two elements of `E` lifting non-chaining stable transvections commute in `E`. -/
private theorem commute_of_apply_eq_stableTransvection
    {q : E →* StableGeneralLinearGroup R}
    (hq_range : q.range = StableGeneralLinearGroup.elementarySubgroup R)
    (hq_ker : q.ker ≤ Subgroup.center E)
    {i j k l : ℕ} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    {a b : R} {w x : E}
    (hw : q w = stableTransvection ⟨(i, j), hij⟩ a)
    (hx : q x = stableTransvection ⟨(k, l), hkl⟩ b) : Commute w x := by
  let m := max (max i j) (max k l) + 1
  have hkm : k ≠ m := by omega
  have hml : m ≠ l := by omega
  obtain ⟨u, hu⟩ : ∃ u : E, q u = stableTransvection ⟨(k, m), hkm⟩ b := by
    have hmem := stableTransvection_mem_elementarySubgroup ⟨(k, m), hkm⟩ b
    rwa [← hq_range] at hmem
  obtain ⟨v, hv⟩ : ∃ v : E, q v = stableTransvection ⟨(m, l), hml⟩ 1 := by
    have hmem := stableTransvection_mem_elementarySubgroup ⟨(m, l), hml⟩ (1 : R)
    rwa [← hq_range] at hmem
  have hcomm_uv : Commute w ⁅u, v⁆ :=
    MonoidHom.commute_commutatorElement_of_commute_of_ker_le_center hq_ker
      (by rw [hw, hu]; exact commute_stableTransvection hij hkm hjk (by omega) a b)
      (by rw [hw, hv]; exact commute_stableTransvection hij hml (by omega) hli a 1)
  have hquv : q ⁅u, v⁆ = q x := by
    rw [map_commutatorElement, hu, hv, commutatorElement_stableTransvection hkm hml hkl, mul_one,
      hx]
  have hz : ⁅u, v⁆⁻¹ * x ∈ Subgroup.center E := hq_ker <| by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hquv, inv_mul_cancel]
  have hcomm_z : Commute w (⁅u, v⁆⁻¹ * x) := Subgroup.mem_center_iff.mp hz w
  simpa only [mul_inv_cancel_left] using hcomm_uv.mul_right hcomm_z

/-- Four-index associativity of commutators of lifted transvections: for pairwise distinct indices
`i, m₁, m₂, j`, `⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆`. -/
private theorem commutatorElement_assoc_of_apply_eq
    {q : E →* StableGeneralLinearGroup R}
    (hq_range : q.range = StableGeneralLinearGroup.elementarySubgroup R)
    (hq_ker : q.ker ≤ Subgroup.center E)
    {i m₁ m₂ j : ℕ} (hi_m1 : i ≠ m₁) (hi_m2 : i ≠ m₂) (hij : i ≠ j)
    (hm1_m2 : m₁ ≠ m₂) (hm1_j : m₁ ≠ j) (hm2_j : m₂ ≠ j)
    {a b c : R} {x y z : E}
    (hx : q x = stableTransvection ⟨(i, m₁), hi_m1⟩ a)
    (hy : q y = stableTransvection ⟨(m₁, m₂), hm1_m2⟩ b)
    (hz : q z = stableTransvection ⟨(m₂, j), hm2_j⟩ c) :
    ⁅x, ⁅y, z⁆⁆ = ⁅⁅x, y⁆, z⁆ := by
  have hq_xy : q ⁅x, y⁆ = stableTransvection ⟨(i, m₂), hi_m2⟩ (a * b) := by
    rw [map_commutatorElement, hx, hy, commutatorElement_stableTransvection hi_m1 hm1_m2 hi_m2]
  have hq_yz : q ⁅y, z⁆ = stableTransvection ⟨(m₁, j), hm1_j⟩ (b * c) := by
    rw [map_commutatorElement, hy, hz, commutatorElement_stableTransvection hm1_m2 hm2_j hm1_j]
  have hq_xyz : q ⁅⁅x, y⁆, z⁆ = stableTransvection ⟨(i, j), hij⟩ (a * b * c) := by
    rw [map_commutatorElement, hq_xy, hz, commutatorElement_stableTransvection hi_m2 hm2_j hij]
  have hxz : Commute x z :=
    commute_of_apply_eq_stableTransvection hq_range hq_ker hi_m1 hm2_j hm1_m2 hij.symm hx hz
  have hxy_yz : Commute ⁅x, y⁆ ⁅y, z⁆ :=
    commute_of_apply_eq_stableTransvection hq_range hq_ker hi_m2 hm1_j hm1_m2.symm hij.symm
      hq_xy hq_yz
  have hyz_xyz : Commute ⁅y, z⁆ ⁅⁅x, y⁆, z⁆ :=
    commute_of_apply_eq_stableTransvection hq_range hq_ker hm1_j hij hij.symm hm1_j.symm
      hq_yz hq_xyz
  have hconj_xz : x * z * x⁻¹ = z := by rw [hxz.eq, mul_inv_cancel_right]
  have hyz_mul : y * z * y⁻¹ = ⁅y, z⁆ * z := by simp only [commutatorElement_def]; group
  have hstep1 : x * (y * z * y⁻¹) * x⁻¹ = ⁅x, y⁆ * (y * (x * z * x⁻¹) * y⁻¹) * ⁅x, y⁆⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [hconj_xz, hyz_mul] at hstep1
  have hlhs : x * (⁅y, z⁆ * z) * x⁻¹ = ⁅x, ⁅y, z⁆⁆ * ⁅y, z⁆ * z := by
    calc
      x * (⁅y, z⁆ * z) * x⁻¹ = (x * ⁅y, z⁆ * x⁻¹) * (x * z * x⁻¹) := by group
      _ = ⁅x, ⁅y, z⁆⁆ * ⁅y, z⁆ * z := by
        rw [hconj_xz]
        simp only [commutatorElement_def]
        group
  have hrhs : ⁅x, y⁆ * (⁅y, z⁆ * z) * ⁅x, y⁆⁻¹ = ⁅⁅x, y⁆, z⁆ * ⁅y, z⁆ * z := by
    calc
      ⁅x, y⁆ * (⁅y, z⁆ * z) * ⁅x, y⁆⁻¹
        = (⁅x, y⁆ * ⁅y, z⁆ * ⁅x, y⁆⁻¹) * (⁅x, y⁆ * z * ⁅x, y⁆⁻¹) := by group
      _ = ⁅y, z⁆ * (⁅⁅x, y⁆, z⁆ * z) := by
        rw [hxy_yz.eq, mul_inv_cancel_right]
        simp only [commutatorElement_def]
        group
      _ = ⁅⁅x, y⁆, z⁆ * ⁅y, z⁆ * z := by
        rw [← mul_assoc, hyz_xyz.eq]
  exact mul_right_cancel (mul_right_cancel (hlhs.symm.trans (hstep1.trans hrhs)))

/-- Chosen lift in `E` of `stableTransvection p a` along a central extension `q` of `E_∞(R)`. -/
private def chooseLift {q : E →* StableGeneralLinearGroup R}
    (hq_range : q.range = StableGeneralLinearGroup.elementarySubgroup R)
    (p : {p : ℕ × ℕ // p.1 ≠ p.2}) (a : R) : E :=
  (hq_range.symm ▸ stableTransvection_mem_elementarySubgroup p a).choose

private theorem apply_chooseLift {q : E →* StableGeneralLinearGroup R}
    (hq_range : q.range = StableGeneralLinearGroup.elementarySubgroup R)
    (p : {p : ℕ × ℕ // p.1 ≠ p.2}) (a : R) :
    q (chooseLift hq_range p a) = stableTransvection p a :=
  (hq_range.symm ▸ stableTransvection_mem_elementarySubgroup p a).choose_spec

/-- Canonical lift in `E` of the Steinberg generator `x_{ij}(a)`, defined as
`⁅chooseLift (i, m) a, chooseLift (m, j) 1⁆` at `m = max i j + 1`. -/
private def liftGen {q : E →* StableGeneralLinearGroup R}
    (hq_range : q.range = StableGeneralLinearGroup.elementarySubgroup R)
    ⦃i j : ℕ⦄ (_ : i ≠ j) (a : R) : E :=
  ⁅chooseLift hq_range ⟨(i, max i j + 1), by omega⟩ a,
    chooseLift hq_range ⟨(max i j + 1, j), by omega⟩ 1⁆

private theorem apply_liftGen {q : E →* StableGeneralLinearGroup R}
    (hq_range : q.range = StableGeneralLinearGroup.elementarySubgroup R)
    {i j : ℕ} (hij : i ≠ j) (a : R) :
    q (liftGen hq_range hij a) = stableTransvection ⟨(i, j), hij⟩ a := by
  rw [liftGen, map_commutatorElement, apply_chooseLift, apply_chooseLift,
    commutatorElement_stableTransvection _ _ hij, mul_one]

private theorem commutatorElement_eq_chooseLift_of_gt
    {q : E →* StableGeneralLinearGroup R}
    (hq_range : q.range = StableGeneralLinearGroup.elementarySubgroup R)
    (hq_ker : q.ker ≤ Subgroup.center E)
    {i k j M : ℕ} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (hiM : i < M) (hjM : j < M) (hkM : k < M)
    {a b : R} {u v : E}
    (hu : q u = stableTransvection ⟨(i, k), hik⟩ a)
    (hv : q v = stableTransvection ⟨(k, j), hkj⟩ b) :
    ⁅u, v⁆ =
      ⁅chooseLift hq_range ⟨(i, M), hiM.ne⟩ (a * b),
        chooseLift hq_range ⟨(M, j), hjM.ne.symm⟩ 1⁆ := by
  let v₁ := chooseLift hq_range ⟨(k, M), hkM.ne⟩ b
  let v₂ := chooseLift hq_range ⟨(M, j), hjM.ne.symm⟩ 1
  have hv12 : q ⁅v₁, v₂⁆ = q v := by
    rw [map_commutatorElement, apply_chooseLift, apply_chooseLift,
      commutatorElement_stableTransvection hkM.ne hjM.ne.symm hkj, mul_one, hv]
  calc
    ⁅u, v⁆ = ⁅u, ⁅v₁, v₂⁆⁆ := MonoidHom.commutatorElement_eq_of_ker_le_center hq_ker rfl hv12.symm
    _ = ⁅⁅u, v₁⁆, v₂⁆ := commutatorElement_assoc_of_apply_eq hq_range hq_ker
      hik hiM.ne hij hkM.ne hkj hjM.ne.symm hu (apply_chooseLift hq_range _ b)
      (apply_chooseLift hq_range _ 1)
    _ = ⁅chooseLift hq_range ⟨(i, M), hiM.ne⟩ (a * b), v₂⁆ :=
      MonoidHom.commutatorElement_eq_of_ker_le_center hq_ker
        (by rw [map_commutatorElement, hu, apply_chooseLift, apply_chooseLift,
          commutatorElement_stableTransvection hik hkM.ne hiM.ne]) rfl

/-- For **any** intermediate index `k` (`i ≠ k`, `k ≠ j`) and any lifts `u, v ∈ E` of
`e_{ik}(a)` and `e_{kj}(b)`, their commutator in `E` equals `liftGen hij (a * b)`. -/
private theorem commutatorElement_eq_liftGen
    {q : E →* StableGeneralLinearGroup R}
    (hq_range : q.range = StableGeneralLinearGroup.elementarySubgroup R)
    (hq_ker : q.ker ≤ Subgroup.center E)
    {i k j : ℕ} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    {a b : R} {u v : E}
    (hu : q u = stableTransvection ⟨(i, k), hik⟩ a)
    (hv : q v = stableTransvection ⟨(k, j), hkj⟩ b) :
    ⁅u, v⁆ = liftGen hq_range hij (a * b) := by
  let m := max i j + 1
  let M := max m k + 1
  have h1 := commutatorElement_eq_chooseLift_of_gt hq_range hq_ker hij hik hkj
    (M := M) (by omega) (by omega) (by omega) hu hv
  have h2 := commutatorElement_eq_chooseLift_of_gt hq_range hq_ker hij
    (k := m) (by omega) (by omega) (M := M) (by omega) (by omega) (by omega)
    (apply_chooseLift hq_range ⟨(i, m), by omega⟩ (a * b))
    (apply_chooseLift hq_range ⟨(m, j), by omega⟩ 1)
  rw [mul_one] at h2
  exact h1.trans h2.symm

private theorem liftGen_add {q : E →* StableGeneralLinearGroup R}
    (hq_range : q.range = StableGeneralLinearGroup.elementarySubgroup R)
    (hq_ker : q.ker ≤ Subgroup.center E)
    {i j : ℕ} (hij : i ≠ j) (a b : R) :
    liftGen hq_range hij (a + b) = liftGen hq_range hij a * liftGen hq_range hij b := by
  let m := max i j + 1
  have him : i ≠ m := by omega
  have hmj : m ≠ j := by omega
  have hprod : q (liftGen hq_range him a * liftGen hq_range him b) =
      stableTransvection ⟨(i, m), him⟩ (a + b) := by
    rw [map_mul, apply_liftGen, apply_liftGen, stableTransvection_add]
  have h1 := commutatorElement_eq_liftGen hq_range hq_ker hij him hmj hprod
    (apply_liftGen hq_range hmj 1)
  rw [mul_one, commutatorElement_mul_left_eq_conj_mul,
    commutatorElement_eq_liftGen hq_range hq_ker hij him hmj
      (apply_liftGen hq_range him b) (apply_liftGen hq_range hmj 1),
    commutatorElement_eq_liftGen hq_range hq_ker hij him hmj
      (apply_liftGen hq_range him a) (apply_liftGen hq_range hmj 1),
    mul_one, mul_one] at h1
  have hcomm_im : Commute (liftGen hq_range him a) (liftGen hq_range hij b) :=
    commute_of_apply_eq_stableTransvection hq_range hq_ker him hij him.symm hij.symm
      (apply_liftGen hq_range him a) (apply_liftGen hq_range hij b)
  have hcomm_ij : Commute (liftGen hq_range hij b) (liftGen hq_range hij a) :=
    commute_of_apply_eq_stableTransvection hq_range hq_ker hij hij hij.symm hij.symm
      (apply_liftGen hq_range hij b) (apply_liftGen hq_range hij a)
  rw [← h1, hcomm_im.eq, mul_inv_cancel_right, hcomm_ij.eq]

/-- **Steinberg lift into a central extension of `E_∞(R)`.** Given any group `E` and homomorphism
`q : E →* GL_∞(R)` with image `E_∞(R)` and central kernel, there is a canonical homomorphism
`St(R) →* E` over `GL_∞(R)`. -/
def liftCentralExtension {q : E →* StableGeneralLinearGroup R}
    (hq_range : q.range = StableGeneralLinearGroup.elementarySubgroup R)
    (hq_ker : q.ker ≤ Subgroup.center E) : SteinbergGroup R →* E :=
  IndexedSteinbergGroup.lift (liftGen hq_range)
    (fun _ _ hij a b ↦ liftGen_add hq_range hq_ker hij a b)
    (fun _ _ _ _ hij hkl hjk hli a b ↦
      commute_of_apply_eq_stableTransvection hq_range hq_ker hij hkl hjk hli
        (apply_liftGen hq_range hij a) (apply_liftGen hq_range hkl b))
    (fun _ _ _ hij hjk hik a b ↦
      commutatorElement_eq_liftGen hq_range hq_ker hik hij hjk
        (apply_liftGen hq_range hij a) (apply_liftGen hq_range hjk b))

@[simp]
theorem comp_liftCentralExtension {q : E →* StableGeneralLinearGroup R}
    (hq_range : q.range = StableGeneralLinearGroup.elementarySubgroup R)
    (hq_ker : q.ker ≤ Subgroup.center E) :
    q.comp (liftCentralExtension hq_range hq_ker) = toStableGL R := by
  ext i j hij a
  simp [liftCentralExtension, apply_liftGen]

@[simp]
theorem apply_liftCentralExtension {q : E →* StableGeneralLinearGroup R}
    (hq_range : q.range = StableGeneralLinearGroup.elementarySubgroup R)
    (hq_ker : q.ker ≤ Subgroup.center E) (z : SteinbergGroup R) :
    q (liftCentralExtension hq_range hq_ker z) = toStableGL R z :=
  DFunLike.congr_fun (comp_liftCentralExtension hq_range hq_ker) z

/-- **Universal property of `St(R)` over `GL_∞(R)`**: for every group `E` (in any universe) and
homomorphism `q : E →* GL_∞(R)` with image `E_∞(R)` and central kernel, there is a unique
homomorphism `ψ : St(R) →* E` satisfying `q ∘ ψ = toStableGL R`. -/
theorem existsUnique_comp_eq_toStableGL (q : E →* StableGeneralLinearGroup R)
    (hq_range : q.range = StableGeneralLinearGroup.elementarySubgroup R)
    (hq_ker : q.ker ≤ Subgroup.center E) :
    ∃! ψ : SteinbergGroup R →* E, q.comp ψ = toStableGL R := by
  refine ⟨liftCentralExtension hq_range hq_ker, comp_liftCentralExtension hq_range hq_ker, ?_⟩
  intro ψ hψ
  exact MonoidHom.eq_of_comp_eq_of_ker_le_center hq_ker
    (hψ.trans (comp_liftCentralExtension hq_range hq_ker).symm)

variable (R) in
/-- **The projection `St(R) →* E_∞(R)` is a universal central extension** in the sense of
`MonoidHom.IsUniversalCentralExtension`, with respect to central extensions in any universe `v`. -/
theorem isUniversalCentralExtension_toElementarySubgroup :
    (toElementarySubgroup R).IsUniversalCentralExtension.{v} where
  isCentralExtension := isCentralExtension_toElementarySubgroup
  existsUnique_comp_eq := by
    intro E' _ q' hq'
    let q : E' →* StableGeneralLinearGroup R :=
      (StableGeneralLinearGroup.elementarySubgroup R).subtype.comp q'
    have hq_range : q.range = StableGeneralLinearGroup.elementarySubgroup R := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hq'.surjective, Subgroup.map_top,
        Subgroup.range_subtype]
    have hq_ker : q.ker ≤ Subgroup.center E' := by
      have hker : q.ker = q'.ker := by
        ext x
        simp [q, MonoidHom.mem_ker]
      exact hker ▸ hq'.ker_le_center
    obtain ⟨ψ, hψ, huniq⟩ := existsUnique_comp_eq_toStableGL q hq_range hq_ker
    refine ⟨ψ, ?_, fun φ hφ ↦ huniq φ ?_⟩
    · refine MonoidHom.ext fun z ↦ Subtype.ext (DFunLike.congr_fun hψ z)
    · refine MonoidHom.ext fun z ↦ congrArg Subtype.val (DFunLike.congr_fun hφ z)

end Universal

end SteinbergGroup

/-- **Kervaire–Steinberg universal central extension theorem.** For every associative unital ring
`R`, the homomorphism `φ = SteinbergGroup.toStableGL R : St(R) →* GL_∞(R)` sending each generator
`x_{ij}(a)` to `stableTransvection ⟨(i, j), hij⟩ a` has image `E_∞(R)` and central kernel, and for
every group `E` (in any universe) and homomorphism `q : E →* GL_∞(R)` with image `E_∞(R)` and
central kernel there is a unique homomorphism `ψ : St(R) →* E` with `q ∘ ψ = φ`. -/
theorem steinberg_universalCentralExtension (R : Type u) [Ring R] :
    ∃ φ : SteinbergGroup R →* StableGeneralLinearGroup R,
      (∀ p a, φ (PresentedGroup.of (p, a)) = stableTransvection p a) ∧
      φ.range = StableGeneralLinearGroup.elementarySubgroup R ∧
      φ.ker ≤ Subgroup.center (SteinbergGroup R) ∧
      ∀ (E : Type v) [Group E] (q : E →* StableGeneralLinearGroup R),
        q.range = StableGeneralLinearGroup.elementarySubgroup R →
        q.ker ≤ Subgroup.center E →
        ∃! ψ : SteinbergGroup R →* E, q.comp ψ = φ :=
  ⟨SteinbergGroup.toStableGL R, SteinbergGroup.toStableGL_of, SteinbergGroup.range_toStableGL,
    SteinbergGroup.ker_toStableGL_le_center,
    fun _ _ q ↦ SteinbergGroup.existsUnique_comp_eq_toStableGL q⟩

end TauCeti
