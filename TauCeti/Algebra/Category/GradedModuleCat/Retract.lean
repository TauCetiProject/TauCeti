/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.CategoryTheory.Retract
public import Mathlib.RingTheory.PrincipalIdealDomain
public import TauCeti.Algebra.Category.GradedModuleCat.Free
import Mathlib.Algebra.Module.Torsion.Pi
import Mathlib.LinearAlgebra.FreeModule.PID
import TauCeti.Algebra.Module.GradedModule.Nakayama

/-!
# Graded retracts of finite graded free modules

Let `k` be a principal ideal domain and `A` a nonnegatively `ℤ`-graded `k`-algebra whose degree-zero
piece is generated over `k` by `1` and is `k`-torsion-free. Every graded retract of a finite graded
free `A`-module is again finite graded free, and every degree-zero idempotent on a finite graded
free `A`-module splits through a finite graded free `A`-module and has a finite homogeneous
`A`-basis for its image.

The proof reduces modulo the positive-degree action `A₊`: on a graded free module `F = ⨁ⱼ A{sⱼ}`,
the degree-`p` piece modulo `A₊ F` identifies with the coordinates `j` of shift `s j = p`, valued
in `𝒜 0`. For a graded retract `M` of `F`, the degree-`p` piece of `M / A₊ M` therefore embeds into
a finitely generated torsion-free `k`-module, hence is finite free over the PID `k`. Choosing finite
`k`-bases in each generating degree `p ∈ range s` and lifting homogeneously gives a degree-zero map
`φ : free 𝒜 d ⟶ M`. Bounded-below graded Nakayama
(`TauCeti.InternalGrading.eq_top_of_piece_le_sup_positive_smul_top`) shows that `φ` is surjective.
Since `M` is a retract of the projective object `F`, `M` is projective and `φ` admits a degree-zero
section, so `ker φ` is a bounded-below summand of `free 𝒜 d` annihilated modulo `A₊`; a second
application of graded Nakayama (`TauCeti.InternalGrading.subsingleton_of_positive_smul_top_eq_top`)
shows that `ker φ = 0`. Thus `φ` is a graded isomorphism.

No commutativity assumption on `A` is needed, and the theorem holds over any PID `k` (in particular
`ℤ` or any field), including the degenerate cases of an empty index set or the zero ring.

## Main definitions

* `TauCeti.GradedModuleCat.retractRangeObj`: the retract structure on `rangeObj p` for a
  degree-zero idempotent `p`.

## Main results

* `TauCeti.GradedModuleCat.mem_free_positive_smul_top_iff`: a homogeneous element of degree `p` in
  `free 𝒜 s` lies in `A₊ (free 𝒜 s)` iff all coordinates of shift `p` vanish.
* `TauCeti.GradedModuleCat.exists_iso_free_of_retract`: every graded retract of a finite graded
  free module over a nonnegatively graded algebra with PID degree-zero piece is graded isomorphic
  to a finite graded free module.
* `TauCeti.GradedModuleCat.exists_homogeneous_basis_of_retract`: every such retract admits a finite
  homogeneous `A`-basis.
* `TauCeti.GradedModuleCat.exists_free_factorization_of_idempotent`: every degree-zero idempotent on
  a finite graded free module factors through a finite graded free module via degree-zero maps
  `ι` and `π` with `ι ≫ π = 𝟙` and `π ≫ ι = p`.
* `TauCeti.GradedModuleCat.exists_homogeneous_basis_range_idempotent`: the image of a degree-zero
  idempotent on a finite graded free module admits a finite homogeneous `A`-basis.
* `TauCeti.GradedModuleCat.exists_homogeneous_basis_range_idempotent_pi` and
  `TauCeti.GradedModuleCat.exists_factorization_idempotent_pi`: the corresponding statements on the
  coordinate module `I → A` for a finite index type `I`.

## References

* C. Năstăsescu and F. Van Oystaeyen, *Methods of Graded Rings*, Section 2.3, for graded modules
  and graded Nakayama.
* L.-H. Robert and E. Wagner, *Symmetric Khovanov–Rozansky link homologies*, J. Éc. polytech. Math.
  7 (2020), 573–651, Section 3.4, for integral graded freeness of idempotent images over weighted
  polynomial rings.
-/

public section

noncomputable section

open CategoryTheory
open scoped DirectSum

namespace TauCeti.GradedModuleCat

universe uk uA v uI

section Range

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} {M N : GradedModuleCat.{v} 𝒜}

/-- The image of a degree-zero idempotent `p : M ⟶ M` is a graded retract of `M`. -/
def retractRangeObj (p : M ⟶ M) (hp : p ≫ p = p) : Retract (rangeObj p) M where
  i := rangeι p
  r := rangeRestrict p
  retract := by
    apply hom_ext
    ext ⟨y, x, hx⟩
    have hp_apply : p.hom (p.hom x) = p.hom x :=
      LinearMap.congr_fun (congrArg Hom.hom hp) x
    simp [← hx, hp_apply]

/-- The inclusion map of `retractRangeObj p hp` is `rangeι p`. -/
@[simp]
theorem retractRangeObj_i (p : M ⟶ M) (hp : p ≫ p = p) :
    (retractRangeObj p hp).i = rangeι p := by
  rfl

/-- The retraction map of `retractRangeObj p hp` is `rangeRestrict p`. -/
@[simp]
theorem retractRangeObj_r (p : M ⟶ M) (hp : p ≫ p = p) :
    (retractRangeObj p hp).r = rangeRestrict p := by
  rfl

/-- Any morphism of graded modules maps the positive-degree action `A₊ M` into `A₊ N`. -/
theorem map_mem_positive_smul_top (f : M ⟶ N) {x : M}
    (hx : x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M)) :
    f.hom x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k N) := by
  refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun u v hu hv => ?_)
  · rw [map_smul]
    exact Submodule.smul_mem_smul ha Submodule.mem_top
  · rw [map_add]
    exact Submodule.add_mem _ hu hv

end Range

section PositiveAction

variable {k : Type uk} [CommRing k] {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- Over a nonnegatively graded algebra, a graded free module vanishes below all its shift
degrees. -/
theorem free_piece_eq_bot_of_forall_lt (hneg : ∀ i < 0, 𝒜 i = ⊥) {I : Type uI} {s : I → ℤ}
    {p : ℤ} (hp : ∀ j, p < s j) : (free 𝒜 s).grading.piece p = ⊥ := by
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  ext j
  have hxj : x j ∈ 𝒜 (p - s j) := (mem_free_piece_iff 𝒜 s p x).mp hx j
  have hbot : 𝒜 (p - s j) = ⊥ := hneg (p - s j) (sub_neg.mpr (hp j))
  rw [hbot] at hxj
  simpa using hxj

/-- Over a nonnegatively graded algebra, a homogeneous element of degree `p` in `free 𝒜 s` lies in
`A₊ (free 𝒜 s)` iff every coordinate whose shift equals `p` vanishes. -/
theorem mem_free_positive_smul_top_iff (hneg : ∀ i < 0, 𝒜 i = ⊥) {I : Type uI} {s : I → ℤ}
    {p : ℤ} {x : free 𝒜 s} (hx : x ∈ (free 𝒜 s).grading.piece p) :
    x ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (free 𝒜 s)) ↔
      ∀ j, s j = p → x j = 0 := by
  classical
  let : SetLike.GradedSMul 𝒜 (free 𝒜 s).grading.piece := (free 𝒜 s).gradedSMul
  constructor
  · intro hpos j hj
    have hspan :=
      InternalGrading.decompose_mem_span_of_mem_positive_smul_top 𝒜 (G := (free 𝒜 s).grading)
        hpos p
    rw [_root_.DirectSum.decompose_of_mem_same (free 𝒜 s).grading.piece hx] at hspan
    let comp : free 𝒜 s →ₗ[k] A := (DirectSum.component A I (fun _ => A) j).restrictScalars k
    have hle : Submodule.span k
        {z : free 𝒜 s | ∃ i, 0 < i ∧ ∃ a ∈ 𝒜 i,
          ∃ y ∈ (free 𝒜 s).grading.piece (p - i), a • y = z} ≤
        LinearMap.ker comp := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨i, hi, a, -, y, hy, rfl⟩
      have hyj : y j ∈ 𝒜 (p - i - s j) := (mem_free_piece_iff 𝒜 s (p - i) y).mp hy j
      have hbot : 𝒜 (p - i - s j) = ⊥ := hneg _ (by omega)
      rw [hbot, Submodule.mem_bot] at hyj
      exact mul_eq_zero_of_right a hyj
    exact hle hspan
  · intro hzero
    rw [← (freeBasis 𝒜 s).linearCombination_repr x, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [freeBasis_repr_apply, freeBasis_apply]
    have hxj : x j ∈ 𝒜 (p - s j) := (mem_free_piece_iff 𝒜 s p x).mp hx j
    rcases lt_trichotomy (p - s j) 0 with hlt | heq | hgt
    · rw [hneg _ hlt, Submodule.mem_bot] at hxj
      rw [hxj, zero_smul]
      exact Submodule.zero_mem _
    · rw [hzero j (by omega), zero_smul]
      exact Submodule.zero_mem _
    · exact Submodule.smul_mem_smul
        (Submodule.mem_iSup_of_mem (p - s j) (Submodule.mem_iSup_of_mem hgt hxj))
        Submodule.mem_top

/-- If `𝒜 0` is generated over `k` by `1`, then `𝒜 0` is a finitely generated `k`-module. -/
private theorem finite_zero_piece (hzero : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a) :
    Module.Finite k (𝒜 0) := by
  let f : k →ₗ[k] 𝒜 0 :=
    (Algebra.linearMap k A).codRestrict (𝒜 0) fun c => by
      rw [Algebra.linearMap_apply, Algebra.algebraMap_eq_smul_one]
      exact (𝒜 0).smul_mem c (SetLike.one_mem_graded 𝒜)
  refine Module.Finite.of_surjective f fun ⟨a, ha⟩ => ?_
  obtain ⟨c, hc⟩ := hzero a ha
  exact ⟨c, Subtype.ext hc⟩

/-- The `k`-linear map reading the degree-`p` coordinates of `h.i` in `𝒜 0` on a retract `M` of
`free 𝒜 s`. -/
private def evalZeroPiece {I : Type} {s : I → ℤ} {M : GradedModuleCat.{uA} 𝒜}
    (h : Retract M (free 𝒜 s)) (p : ℤ) :
    M.grading.piece p →ₗ[k] ({j : I // s j = p} → 𝒜 0) where
  toFun x j :=
    ⟨(h.i.hom x.1) j.1, by
      have := (mem_free_piece_iff 𝒜 s p (h.i.hom x.1)).mp (map_mem h.i x.2) j.1
      simpa [j.2] using this⟩
  map_add' x y := by
    ext j
    simp
  map_smul' c x := by
    ext j
    have hsmul : (c • h.i.hom x.1) j.1 = c • (h.i.hom x.1) j.1 := by
      rw [← algebraMap_smul A c (h.i.hom x.1), ← algebraMap_smul A c ((h.i.hom x.1) j.1)]
      exact DFinsupp.smul_apply (algebraMap k A c) (h.i.hom x.1) j.1
    simpa [Submodule.coe_smul_of_tower] using hsmul

/-- The kernel of `evalZeroPiece` is precisely `M_p ∩ A₊ M`. -/
private theorem evalZeroPiece_eq_zero_iff (hneg : ∀ i < 0, 𝒜 i = ⊥) {I : Type} {s : I → ℤ}
    {M : GradedModuleCat.{uA} 𝒜} (h : Retract M (free 𝒜 s)) (p : ℤ) (x : M.grading.piece p) :
    evalZeroPiece h p x = 0 ↔
      (x : M) ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
  have heval : evalZeroPiece h p x = 0 ↔ ∀ j : I, s j = p → (h.i.hom x.1) j = 0 := by
    constructor
    · intro hx j hj
      have := congrArg (fun f : {j : I // s j = p} → 𝒜 0 => (f ⟨j, hj⟩ : A)) hx
      simpa [evalZeroPiece] using this
    · intro hx
      ext ⟨j, hj⟩
      exact hx j hj
  rw [heval, ← mem_free_positive_smul_top_iff hneg (map_mem h.i x.2)]
  constructor
  · intro hpos
    have hr := map_mem_positive_smul_top h.r hpos
    have hri : h.r.hom (h.i.hom x.1) = x.1 :=
      LinearMap.congr_fun (congrArg Hom.hom h.retract) x.1
    rwa [hri] at hr
  · exact map_mem_positive_smul_top h.i

/-- A lower bound on all shift degrees of a finitely indexed family `s : I → ℤ`. -/
private def minShift {I : Type} [Fintype I] (s : I → ℤ) : ℤ :=
  let S : Finset ℤ := Finset.univ.image s
  if hS : S.Nonempty then S.min' hS else 0

private theorem minShift_le {I : Type} [Fintype I] (s : I → ℤ) (j : I) :
    minShift s ≤ s j := by
  have hmem : s j ∈ Finset.univ.image s := Finset.mem_image_of_mem s (Finset.mem_univ j)
  have hS : (Finset.univ.image s).Nonempty := ⟨s j, hmem⟩
  simp only [minShift, hS, ↓reduceDIte]
  exact Finset.min'_le _ (s j) hmem

/-- Subtracting the degree-`p` shifted summands from a degree-`p` element `z` of `free 𝒜 d` leaves
an element of `A₊ (free 𝒜 d)`. -/
private theorem sub_sum_freeGenerator_mem_positive_smul_top
    (hneg : ∀ i < 0, 𝒜 i = ⊥) {N : ℕ} {d : Fin N → ℤ} {p : ℤ}
    {J₀ : Type} [Fintype J₀] (idx : J₀ → Fin N)
    (hidx_inj : Function.Injective idx)
    (hidx_deg : ∀ r, d (idx r) = p)
    (hidx_surj : ∀ t, d t = p → ∃ r, idx r = t)
    {z : free 𝒜 d} (hz : z ∈ (free 𝒜 d).grading.piece p) :
    z - ∑ r : J₀, z (idx r) • freeGenerator (𝒜 := 𝒜) (d := d) (idx r) ∈
      (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (free 𝒜 d)) := by
  classical
  let : SetLike.GradedSMul 𝒜 (free 𝒜 d).grading.piece := (free 𝒜 d).gradedSMul
  have hz₀_mem : ∑ r : J₀, z (idx r) • freeGenerator (𝒜 := 𝒜) (d := d) (idx r) ∈
      (free 𝒜 d).grading.piece p := by
    refine (free 𝒜 d).grading.piece p |>.sum_mem fun r _ => ?_
    have hcoeff : z (idx r) ∈ 𝒜 0 := by
      have := (mem_free_piece_iff 𝒜 d p z).mp hz (idx r)
      simpa [hidx_deg r] using this
    have hgen : freeGenerator (𝒜 := 𝒜) (d := d) (idx r) ∈ (free 𝒜 d).grading.piece p :=
      hidx_deg r ▸ freeGenerator_mem_free_piece (𝒜 := 𝒜) (d := d) (idx r)
    simpa using SetLike.GradedSMul.smul_mem (B := (free 𝒜 d).grading.piece) hcoeff hgen
  refine (mem_free_positive_smul_top_iff hneg
    ((free 𝒜 d).grading.piece p |>.sub_mem hz hz₀_mem)).mpr fun t ht => ?_
  obtain ⟨r₀, rfl⟩ := hidx_surj t ht
  rw [DFinsupp.sub_apply, sub_eq_zero, DFinsupp.finsetSum_apply, Finset.sum_eq_single r₀]
  · rw [DFinsupp.smul_apply, freeGenerator_apply]
    simp
  · intro r _ hrr₀
    rw [DFinsupp.smul_apply, freeGenerator_apply]
    simp [hidx_inj.ne hrr₀]
  · intro hnot
    exact absurd (Finset.mem_univ r₀) hnot

/-- A finite `k`-basis of `range (evalZeroPiece h p)` lifted homogeneously to `M_p` for each shift
degree `p ∈ Finset.univ.image s` induces a graded surjection from the corresponding finite graded
free module. -/
private theorem surjective_freeLift_of_evalZeroPiece_basis
    (hneg : ∀ i < 0, 𝒜 i = ⊥) {I : Type} [Fintype I] {s : I → ℤ} {M : GradedModuleCat.{uA} 𝒜}
    (h : Retract M (free 𝒜 s))
    (degRank : ℤ → ℕ)
    (degBasis : ∀ p, Module.Basis (Fin (degRank p)) k (LinearMap.range (evalZeroPiece h p)))
    (liftVec : ∀ p, Fin (degRank p) → M.grading.piece p)
    (hliftVec : ∀ p r, evalZeroPiece h p (liftVec p r) = (degBasis p r : {j : I // s j = p} → 𝒜 0))
    {N : ℕ} (eJ : Fin N ≃ (Σ p : Finset.univ.image s, Fin (degRank p.1))) :
    Function.Surjective
      (freeLift (d := fun t => (eJ t).1.1) (fun t => liftVec (eJ t).1.1 (eJ t).2)).hom := by
  classical
  let S : Finset ℤ := Finset.univ.image s
  let d : Fin N → ℤ := fun t => (eJ t).1.1
  let v : ∀ t : Fin N, M.grading.piece (d t) := fun t => liftVec (eJ t).1.1 (eJ t).2
  let φ : free 𝒜 d ⟶ M := freeLift v
  let liftOfJ (q : Σ p : S, Fin (degRank p.1)) : M := (liftVec q.1.1 q.2 : M)
  have hφ_gen (p : ℤ) (hp : p ∈ S) (r : Fin (degRank p)) :
      φ.hom (freeGenerator (𝒜 := 𝒜) (d := d) (eJ.symm ⟨⟨p, hp⟩, r⟩)) = (liftVec p r : M) := by
    have hv_coe (t : Fin N) : (v t : M) = liftOfJ (eJ t) := rfl
    dsimp only [φ]
    rw [freeLift_generator, hv_coe, eJ.apply_symm_apply]
  have hMbelow : ∀ p < minShift s, M.grading.piece p = ⊥ := fun p hp => by
    have hr_surj : Function.Surjective h.r.hom := fun y =>
      ⟨h.i.hom y, LinearMap.congr_fun (congrArg Hom.hom h.retract) y⟩
    exact piece_eq_bot_of_surjective h.r hr_surj p
      (free_piece_eq_bot_of_forall_lt hneg fun j => lt_of_lt_of_le hp (minShift_le s j))
  -- Apply bounded-below graded Nakayama to `range φ.hom`.
  rw [← LinearMap.range_eq_top]
  refine InternalGrading.eq_top_of_piece_le_sup_positive_smul_top 𝒜 (LinearMap.range φ.hom)
    φ.isHomogeneous.isHomogeneous_range (minShift s) hMbelow fun p x hx => ?_
  by_cases hp : p ∈ S
  · let y : LinearMap.range (evalZeroPiece h p) := ⟨evalZeroPiece h p ⟨x, hx⟩, ⟨⟨x, hx⟩, rfl⟩⟩
    let c : Fin (degRank p) → k := fun t => (degBasis p).repr y t
    let u : free 𝒜 d :=
      ∑ t : Fin (degRank p), algebraMap k A (c t) • freeGenerator (eJ.symm ⟨⟨p, hp⟩, t⟩)
    have hφu : φ.hom u = ∑ t : Fin (degRank p), c t • (liftVec p t : M) := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [map_smul, hφ_gen p hp t, algebraMap_smul]
    have hφu_mem : φ.hom u ∈ M.grading.piece p := by
      rw [hφu]
      exact (M.grading.piece p).sum_mem fun t _ =>
        (M.grading.piece p).smul_mem (c t) (liftVec p t).property
    have heval_u : evalZeroPiece h p ⟨φ.hom u, hφu_mem⟩ = evalZeroPiece h p ⟨x, hx⟩ := by
      have hsum_piece : (⟨φ.hom u, hφu_mem⟩ : M.grading.piece p) =
          ∑ t : Fin (degRank p), c t • liftVec p t := by
        apply Subtype.ext
        rw [AddSubmonoidClass.coe_finsetSum]
        exact hφu
      rw [hsum_piece, map_sum]
      have hrepr := congrArg Subtype.val ((degBasis p).sum_repr y)
      rw [AddSubmonoidClass.coe_finsetSum] at hrepr
      simpa only [map_smul, hliftVec, SetLike.val_smul, c, y] using hrepr
    have hsub_pos : x - φ.hom u ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
      refine (evalZeroPiece_eq_zero_iff hneg h p
        ⟨x - φ.hom u, (M.grading.piece p).sub_mem hx hφu_mem⟩).mp ?_
      have hsub_eq :
          (⟨x - φ.hom u, (M.grading.piece p).sub_mem hx hφu_mem⟩ : M.grading.piece p) =
            ⟨x, hx⟩ - ⟨φ.hom u, hφu_mem⟩ := rfl
      rw [hsub_eq, map_sub, heval_u, sub_self]
    have hx_eq : x = φ.hom u + (x - φ.hom u) := by abel
    rw [hx_eq]
    exact Submodule.add_mem_sup ⟨u, rfl⟩ hsub_pos
  · have hzero_eval : evalZeroPiece h p ⟨x, hx⟩ = 0 := by
      ext ⟨j, hj⟩
      exact absurd (hj ▸ Finset.mem_image_of_mem s (Finset.mem_univ j)) hp
    exact Submodule.mem_sup_right ((evalZeroPiece_eq_zero_iff hneg h p ⟨x, hx⟩).mp hzero_eval)

/-- Every homogeneous element in the kernel of the lifted map `freeLift` from a `k`-basis of
`range (evalZeroPiece h p)` lies in `A₊ (free 𝒜 d)`. -/
private theorem ker_freeLift_mem_positive_smul_top_of_evalZeroPiece_basis
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a)
    {I : Type} [Fintype I] {s : I → ℤ} {M : GradedModuleCat.{uA} 𝒜}
    (h : Retract M (free 𝒜 s))
    (degRank : ℤ → ℕ)
    (degBasis : ∀ p, Module.Basis (Fin (degRank p)) k (LinearMap.range (evalZeroPiece h p)))
    (liftVec : ∀ p, Fin (degRank p) → M.grading.piece p)
    (hliftVec : ∀ p r, evalZeroPiece h p (liftVec p r) = (degBasis p r : {j : I // s j = p} → 𝒜 0))
    {N : ℕ} (eJ : Fin N ≃ (Σ p : Finset.univ.image s, Fin (degRank p.1)))
    (p : ℤ) (z : free 𝒜 (fun t => (eJ t).1.1))
    (hz_free : z ∈ (free 𝒜 (fun t => (eJ t).1.1)).grading.piece p)
    (hφz : (freeLift (d := fun t => (eJ t).1.1) (fun t => liftVec (eJ t).1.1 (eJ t).2)).hom z = 0) :
    z ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (free 𝒜 (fun t => (eJ t).1.1))) := by
  classical
  let S : Finset ℤ := Finset.univ.image s
  let d : Fin N → ℤ := fun t => (eJ t).1.1
  let v : ∀ t : Fin N, M.grading.piece (d t) := fun t => liftVec (eJ t).1.1 (eJ t).2
  let φ : free 𝒜 d ⟶ M := freeLift v
  let liftOfJ (q : Σ p : S, Fin (degRank p.1)) : M := (liftVec q.1.1 q.2 : M)
  have hφ_gen (q : ℤ) (hq : q ∈ S) (r : Fin (degRank q)) :
      φ.hom (freeGenerator (𝒜 := 𝒜) (d := d) (eJ.symm ⟨⟨q, hq⟩, r⟩)) = (liftVec q r : M) := by
    have hv_coe (t : Fin N) : (v t : M) = liftOfJ (eJ t) := rfl
    dsimp only [φ]
    rw [freeLift_generator, hv_coe, eJ.apply_symm_apply]
  refine (mem_free_positive_smul_top_iff hneg hz_free).mpr fun t ht => ?_
  have hp : p ∈ S := ht ▸ (eJ t).1.property
  let idx (r : Fin (degRank p)) : Fin N := eJ.symm ⟨⟨p, hp⟩, r⟩
  let z₀ : free 𝒜 d := ∑ r : Fin (degRank p), z (idx r) • freeGenerator (idx r)
  have hidx_inj : Function.Injective idx := fun r₁ r₂ heq => by
    have h1 := eJ.symm.injective heq
    cases h1
    rfl
  have hidx_deg (r : Fin (degRank p)) : d (idx r) = p := by simp [d, idx]
  have hidx_surj (t' : Fin N) (ht' : d t' = p) : ∃ r, idx r = t' := by
    rcases heJt' : eJ t' with ⟨⟨p', hp'⟩, r₀⟩
    have hp'eq : p' = p := by simpa [d, heJt'] using ht'
    subst hp'eq
    exact ⟨r₀, eJ.injective (by simp [idx, heJt'])⟩
  -- Split off the degree-`p` coordinates `z₀`; the remainder lies in `A₊ (free 𝒜 d)`.
  have hsub_pos : z - z₀ ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (free 𝒜 d)) :=
    sub_sum_freeGenerator_mem_positive_smul_top hneg idx hidx_inj hidx_deg hidx_surj hz_free
  have hφz₀_pos : φ.hom z₀ ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k M) := by
    have h1 := map_mem_positive_smul_top φ hsub_pos
    rw [map_sub, hφz, zero_sub] at h1
    exact (Submodule.neg_mem_iff _).mp h1
  -- The `k`-coefficients of `z₀` vanish by `k`-linear independence of `degBasis p`.
  have hcoeff_mem (r : Fin (degRank p)) : z (idx r) ∈ 𝒜 0 := by
    have := (mem_free_piece_iff 𝒜 d p z).mp hz_free (idx r)
    simpa [d, idx] using this
  choose c hc using fun r => hzero _ (hcoeff_mem r)
  have hφz₀_eq : φ.hom z₀ = ∑ r : Fin (degRank p), c r • (liftVec p r : M) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [map_smul, ← hc r, hφ_gen p hp r, algebraMap_smul]
  have hz₀_mem : φ.hom z₀ ∈ M.grading.piece p := by
    rw [hφz₀_eq]
    exact (M.grading.piece p).sum_mem fun r _ =>
      (M.grading.piece p).smul_mem (c r) (liftVec p r).property
  have hlin : ∑ r : Fin (degRank p), c r • degBasis p r = 0 := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum, ZeroMemClass.coe_zero]
    have hzero_eval := (evalZeroPiece_eq_zero_iff hneg h p ⟨φ.hom z₀, hz₀_mem⟩).mpr hφz₀_pos
    have hpiece_eq : (⟨φ.hom z₀, hz₀_mem⟩ : M.grading.piece p) =
        ∑ r : Fin (degRank p), c r • liftVec p r := by
      apply Subtype.ext
      rw [AddSubmonoidClass.coe_finsetSum]
      exact hφz₀_eq
    rw [hpiece_eq, map_sum] at hzero_eval
    simpa only [map_smul, hliftVec, SetLike.val_smul] using hzero_eval
  have hc_zero (r : Fin (degRank p)) : c r = 0 := by
    have hr := congrArg (fun x => (degBasis p).repr x r) hlin
    simpa [Finsupp.single_apply] using hr
  obtain ⟨r₀, rfl⟩ := hidx_surj t ht
  rw [← hc r₀, hc_zero r₀, map_zero]

/-- If a graded morphism `φ : free 𝒜 d ⟶ M` from a bounded-below graded free module has a
degree-zero section and every homogeneous element of `ker φ` lies in `A₊ (free 𝒜 d)`, then `φ` is
injective by graded Nakayama. -/
private theorem injective_of_section_of_ker_mem_positive_smul_top
    (hneg : ∀ i < 0, 𝒜 i = ⊥) {n : ℕ} {d : Fin n → ℤ} {M : GradedModuleCat.{uA} 𝒜}
    (φ : free 𝒜 d ⟶ M) (σ : M ⟶ free 𝒜 d) (hσφ : σ ≫ φ = 𝟙 M)
    (b₀ : ℤ) (hb₀ : ∀ t, b₀ ≤ d t)
    (hker_pos : ∀ (p : ℤ) (z : free 𝒜 d), z ∈ (free 𝒜 d).grading.piece p → φ.hom z = 0 →
      z ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (free 𝒜 d))) :
    Function.Injective φ.hom := by
  let K : GradedModuleCat.{uA} 𝒜 := kernelObj φ
  let : SetLike.GradedSMul 𝒜 K.grading.piece := K.gradedSMul
  let projK : free 𝒜 d ⟶ K :=
    ofHom (LinearMap.codRestrict (LinearMap.ker φ.hom) (LinearMap.id - σ.hom.comp φ.hom) fun z => by
      have hσφ_apply : φ.hom (σ.hom (φ.hom z)) = φ.hom z :=
        LinearMap.congr_fun (congrArg Hom.hom hσφ) (φ.hom z)
      simp [LinearMap.mem_ker, hσφ_apply]) <|
      LinearMap.isHomogeneous_def.mpr fun p z hz => by
        rw [add_zero, InternalGrading.mem_ker_piece]
        exact (free 𝒜 d).grading.piece p |>.sub_mem hz (map_mem σ (map_mem φ hz))
  have hprojK_id (z : K) : projK.hom (z : free 𝒜 d) = z := by
    apply Subtype.ext
    have hval : (projK.hom (z : free 𝒜 d) : free 𝒜 d) =
        (z : free 𝒜 d) - σ.hom (φ.hom (z : free 𝒜 d)) := rfl
    rw [hval, z.property, map_zero, sub_zero]
  have hKbelow : ∀ p < b₀, K.grading.piece p = ⊥ := fun p hp => by
    apply (Submodule.eq_bot_iff _).mpr
    intro z hz
    apply Subtype.ext
    have hbot := free_piece_eq_bot_of_forall_lt hneg (s := d) fun t =>
      lt_of_lt_of_le hp (hb₀ t)
    have hz' : (z : free 𝒜 d) ∈ (free 𝒜 d).grading.piece p :=
      (InternalGrading.mem_ker_piece _ _).mp hz
    rw [hbot, Submodule.mem_bot] at hz'
    exact hz'
  have hKpos : (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k K) = ⊤ := by
    have htop : (⊤ : Submodule k K) = Submodule.span k {x : K | ∃ p, x ∈ K.grading.piece p} :=
      (K.grading.span_setOf_exists_mem_piece_eq_top k).symm
    refine top_unique (le_of_eq_of_le htop (Submodule.span_le.mpr ?_))
    rintro z ⟨p, hz⟩
    have hz_free : (z : free 𝒜 d) ∈ (free 𝒜 d).grading.piece p :=
      (InternalGrading.mem_ker_piece _ _).mp hz
    rw [← hprojK_id z]
    exact map_mem_positive_smul_top projK (hker_pos p (z : free 𝒜 d) hz_free z.property)
  have hKsub : Subsingleton K :=
    InternalGrading.subsingleton_of_positive_smul_top_eq_top 𝒜 b₀ hKbelow hKpos
  rw [← LinearMap.ker_eq_bot]
  apply (Submodule.eq_bot_iff _).mpr
  intro z hz
  exact congrArg Subtype.val (Subsingleton.elim (⟨z, hz⟩ : K) 0)

/-- Coordinate identification between `free 𝒜 (s ∘ eI.symm)` and `I → A` for a finite index type
`I` with `eI : I ≃ Fin m`. -/
private abbrev freeEquivPi {I : Type uI} {m : ℕ} (eI : I ≃ Fin m) (s : I → ℤ) :
    free 𝒜 (s ∘ eI.symm) ≃ₗ[A] (I → A) :=
  (DirectSum.linearEquivFunOnFintype A (Fin m) (fun _ => A)).trans
    (LinearEquiv.funCongrLeft A A eI)

private theorem freeEquivPi_apply {I : Type uI} {m : ℕ} (eI : I ≃ Fin m) (s : I → ℤ)
    (x : free 𝒜 (s ∘ eI.symm)) (j : I) :
    freeEquivPi (𝒜 := 𝒜) eI s x j = x (eI j) :=
  rfl

private theorem freeEquivPi_symm_apply {I : Type uI} {m : ℕ} (eI : I ≃ Fin m) (s : I → ℤ)
    (v : I → A) (t : Fin m) :
    (freeEquivPi (𝒜 := 𝒜) eI s).symm v t = v (eI.symm t) := by
  have h := congrFun ((freeEquivPi (𝒜 := 𝒜) eI s).apply_symm_apply v) (eI.symm t)
  rw [freeEquivPi_apply, Equiv.apply_symm_apply] at h
  exact h

/-- Transport a degree-zero endomorphism on `I → A` to a morphism on `free 𝒜 (s ∘ eI.symm)`. -/
private def piEndToFree {I : Type uI} {m : ℕ} (eI : I ≃ Fin m) (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    free 𝒜 (s ∘ eI.symm) ⟶ free 𝒜 (s ∘ eI.symm) :=
  let e := freeEquivPi (𝒜 := 𝒜) eI s
  ofHom (e.symm.toLinearMap.comp (p.comp e.toLinearMap)) <|
    LinearMap.isHomogeneous_def.mpr fun d x hx => by
      rw [add_zero, mem_free_piece_iff]
      intro t
      have hx' : ∀ j, e x j ∈ 𝒜 (d - s j) := fun j => by
        rw [freeEquivPi_apply]
        have hj := (mem_free_piece_iff 𝒜 (s ∘ eI.symm) d x).mp hx (eI j)
        simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hj
      rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
        LinearEquiv.coe_toLinearMap, freeEquivPi_symm_apply]
      exact hhom d (e x) hx' (eI.symm t)

private theorem hom_piEndToFree {I : Type uI} {m : ℕ} (eI : I ≃ Fin m) (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    (piEndToFree (𝒜 := 𝒜) eI s p hhom).hom =
      (freeEquivPi (𝒜 := 𝒜) eI s).symm.toLinearMap.comp
        (p.comp (freeEquivPi (𝒜 := 𝒜) eI s).toLinearMap) :=
  rfl

private theorem freeEquivPi_piEndToFree {I : Type uI} {m : ℕ} (eI : I ≃ Fin m) (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j))
    (x : free 𝒜 (s ∘ eI.symm)) :
    freeEquivPi (𝒜 := 𝒜) eI s ((piEndToFree (𝒜 := 𝒜) eI s p hhom).hom x) =
      p (freeEquivPi (𝒜 := 𝒜) eI s x) := by
  rw [hom_piEndToFree, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
    LinearEquiv.coe_toLinearMap, LinearEquiv.apply_symm_apply]

private theorem freeEquivPi_comp_hom_piEndToFree {I : Type uI} {m : ℕ} (eI : I ≃ Fin m) (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A))
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    (freeEquivPi (𝒜 := 𝒜) eI s).toLinearMap.comp (piEndToFree (𝒜 := 𝒜) eI s p hhom).hom =
      p.comp (freeEquivPi (𝒜 := 𝒜) eI s).toLinearMap :=
  LinearMap.ext (freeEquivPi_piEndToFree eI s p hhom)

private theorem piEndToFree_idempotent {I : Type uI} {m : ℕ} (eI : I ≃ Fin m) (s : I → ℤ)
    (p : (I → A) →ₗ[A] (I → A)) (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    piEndToFree (𝒜 := 𝒜) eI s p hhom ≫ piEndToFree (𝒜 := 𝒜) eI s p hhom =
      piEndToFree (𝒜 := 𝒜) eI s p hhom := by
  apply hom_ext
  refine LinearMap.ext fun x => (freeEquivPi (𝒜 := 𝒜) eI s).injective ?_
  rw [hom_comp, LinearMap.comp_apply, freeEquivPi_piEndToFree, freeEquivPi_piEndToFree,
    ← LinearMap.comp_apply, hp]

end PositiveAction

section PIDRetract

variable {k : Type uk} [CommRing k] [IsDomain k] [IsPrincipalIdealRing k]
  {A : Type uA} [Ring A] [Algebra k A]
  {𝒜 : ℤ → Submodule k A} [GradedAlgebra 𝒜]

/-- Construct a graded surjection `φ : free 𝒜 d ⟶ M` from a finite graded free module whose kernel
pieces all lie in `A₊ (free 𝒜 d)` and whose shifts lie in `range s`. -/
private theorem exists_minimal_free_surjection_of_retract [Module.IsTorsionFree k (𝒜 0)]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a)
    {I : Type} [Finite I] {s : I → ℤ} {M : GradedModuleCat.{uA} 𝒜}
    (h : Retract M (free 𝒜 s)) :
    ∃ (n : ℕ) (d : Fin n → ℤ) (φ : free 𝒜 d ⟶ M),
      (∀ t, d t ∈ Set.range s) ∧
      Function.Surjective φ.hom ∧
      ∀ (p : ℤ) (z : free 𝒜 d), z ∈ (free 𝒜 d).grading.piece p → φ.hom z = 0 →
        z ∈ (⨆ (i : ℤ) (_ : 0 < i), 𝒜 i) • (⊤ : Submodule k (free 𝒜 d)) := by
  classical
  cases nonempty_fintype I
  have : Module.Finite k (𝒜 0) := finite_zero_piece hzero
  have hbasis (p : ℤ) :
      ∃ (n : ℕ), Nonempty (Module.Basis (Fin n) k (LinearMap.range (evalZeroPiece h p))) := by
    have : Module.Finite k ({j : I // s j = p} → 𝒜 0) := Module.Finite.pi
    have : Module.Finite k (LinearMap.range (evalZeroPiece h p)) := inferInstance
    have : Module.IsTorsionFree k (LinearMap.range (evalZeroPiece h p)) := inferInstance
    obtain ⟨n, b⟩ :=
      Module.basisOfFiniteTypeTorsionFree' (R := k) (M := LinearMap.range (evalZeroPiece h p))
    exact ⟨n, ⟨b⟩⟩
  choose degRank hbasisNonempty using hbasis
  let degBasis (p : ℤ) : Module.Basis (Fin (degRank p)) k (LinearMap.range (evalZeroPiece h p)) :=
    (hbasisNonempty p).some
  have hlift (p : ℤ) (t : Fin (degRank p)) :
      ∃ x : M.grading.piece p,
        evalZeroPiece h p x = (degBasis p t : {j : I // s j = p} → 𝒜 0) :=
    (degBasis p t).property
  choose liftVec hliftVec using hlift
  let J : Type := Σ p : Finset.univ.image s, Fin (degRank p.1)
  let eJ : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  refine ⟨Fintype.card J, fun t => (eJ t).1.1,
    freeLift (fun t => liftVec (eJ t).1.1 (eJ t).2), ?_, ?_, ?_⟩
  · intro t
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp (eJ t).1.property
    exact ⟨j, hj⟩
  · exact surjective_freeLift_of_evalZeroPiece_basis hneg h degRank degBasis liftVec hliftVec eJ
  · exact ker_freeLift_mem_positive_smul_top_of_evalZeroPiece_basis hneg hzero h degRank degBasis
      liftVec hliftVec eJ

/-- **Graded retracts of finite graded free modules are finite graded free.** Let `k` be a PID and
`A` a nonnegatively `ℤ`-graded `k`-algebra whose degree-zero piece is spanned over `k` by `1` and
`k`-torsion-free. Every graded retract of a finite graded free `A`-module `free 𝒜 s` is graded
isomorphic to `free 𝒜 d` for some finite tuple of shifts `d : Fin n → ℤ`. -/
theorem exists_iso_free_of_retract [Module.IsTorsionFree k (𝒜 0)]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a)
    {I : Type} [Finite I] {s : I → ℤ} {M : GradedModuleCat.{uA} 𝒜}
    (h : Retract M (free 𝒜 s)) :
    ∃ (n : ℕ) (d : Fin n → ℤ), Nonempty (free 𝒜 d ≅ M) := by
  classical
  cases nonempty_fintype I
  obtain ⟨n, d, φ, hd_range, hφ_surj, hker_pos⟩ :=
    exists_minimal_free_surjection_of_retract hneg hzero h
  have : Projective M := h.projective
  have : Epi φ := (epi_iff_surjective φ).mpr hφ_surj
  have hb₀_le_d (t : Fin n) : minShift s ≤ d t := by
    obtain ⟨j, hj⟩ := hd_range t
    exact hj ▸ minShift_le s j
  have hφ_inj : Function.Injective φ.hom :=
    injective_of_section_of_ker_mem_positive_smul_top hneg φ (Projective.factorThru (𝟙 M) φ)
      (Projective.factorThru_comp (𝟙 M) φ) (minShift s) hb₀_le_d hker_pos
  have : IsIso φ := (isIso_iff_bijective φ).mpr ⟨hφ_inj, hφ_surj⟩
  exact ⟨n, d, ⟨asIso φ⟩⟩

/-- **Homogeneous bases of graded retracts.** Under the hypotheses of
`exists_iso_free_of_retract`, every graded retract of `free 𝒜 s` admits a finite homogeneous
`A`-basis. -/
theorem exists_homogeneous_basis_of_retract [Module.IsTorsionFree k (𝒜 0)]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a)
    {I : Type} [Finite I] {s : I → ℤ} {M : GradedModuleCat.{uA} 𝒜}
    (h : Retract M (free 𝒜 s)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A M) (d : Fin n → ℤ),
      ∀ i, b i ∈ M.grading.piece (d i) := by
  obtain ⟨n, d, ⟨e⟩⟩ := exists_iso_free_of_retract hneg hzero h
  exact ⟨n, freeBasisOfIso e, d, freeBasisOfIso_mem_piece e⟩

/-- **Splitting a degree-zero idempotent through a finite graded free module.** Every degree-zero
idempotent `p : free 𝒜 s ⟶ free 𝒜 s` factors through a finite graded free module `free 𝒜 d` via
degree-zero maps `ι` and `π` satisfying `ι ≫ π = 𝟙` and `π ≫ ι = p`. -/
theorem exists_free_factorization_of_idempotent [Module.IsTorsionFree k (𝒜 0)]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a)
    {I : Type} [Finite I] {s : I → ℤ} (p : free 𝒜 s ⟶ free 𝒜 s) (hp : p ≫ p = p) :
    ∃ (n : ℕ) (d : Fin n → ℤ) (ι : free 𝒜 d ⟶ free 𝒜 s) (π : free 𝒜 s ⟶ free 𝒜 d),
      ι ≫ π = 𝟙 (free 𝒜 d) ∧ π ≫ ι = p := by
  obtain ⟨n, d, ⟨e⟩⟩ := exists_iso_free_of_retract hneg hzero (retractRangeObj p hp)
  refine ⟨n, d, e.hom ≫ rangeι p, rangeRestrict p ≫ e.inv, ?_, ?_⟩
  · rw [Category.assoc, ← Category.assoc (rangeι p), ← retractRangeObj_i p hp,
      ← retractRangeObj_r p hp, (retractRangeObj p hp).retract, Category.id_comp, Iso.hom_inv_id]
  · rw [Category.assoc, Iso.inv_hom_id_assoc, rangeRestrict_comp_rangeι]

/-- **Homogeneous bases of idempotent images.** The image of a degree-zero idempotent on a finite
graded free module admits a finite homogeneous `A`-basis. -/
theorem exists_homogeneous_basis_range_idempotent [Module.IsTorsionFree k (𝒜 0)]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a)
    {I : Type} [Finite I] {s : I → ℤ} (p : free 𝒜 s ⟶ free 𝒜 s) (hp : p ≫ p = p) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A (LinearMap.range p.hom)) (d : Fin n → ℤ),
      ∀ i, (b i : free 𝒜 s) ∈ (free 𝒜 s).grading.piece (d i) := by
  obtain ⟨n, b, d, hb⟩ := exists_homogeneous_basis_of_retract hneg hzero (retractRangeObj p hp)
  exact ⟨n, b, d, fun i => (mem_rangeObj_piece_iff p).mp (hb i)⟩

/-- Coordinate-space form of `exists_homogeneous_basis_range_idempotent` on `I → A`, with the `j`-th
summand shifted by `s j` so that degree-`d` elements have `j`-th coordinate in `𝒜 (d - s j)`. -/
theorem exists_homogeneous_basis_range_idempotent_pi [Module.IsTorsionFree k (𝒜 0)]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a)
    {I : Type uI} [Finite I] (s : I → ℤ) (p : (I → A) →ₗ[A] (I → A)) (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    ∃ (n : ℕ) (b : Module.Basis (Fin n) A (LinearMap.range p)) (d : Fin n → ℤ),
      ∀ i j, (b i).val j ∈ 𝒜 (d i - s j) := by
  classical
  cases nonempty_fintype I
  let eI : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let e : free 𝒜 (s ∘ eI.symm) ≃ₗ[A] (I → A) := freeEquivPi (𝒜 := 𝒜) eI s
  let p' := piEndToFree (𝒜 := 𝒜) eI s p hhom
  obtain ⟨n, b', d, hb'⟩ := exists_homogeneous_basis_range_idempotent hneg hzero p'
    (piEndToFree_idempotent eI s p hp hhom)
  let eRange : LinearMap.range p'.hom ≃ₗ[A] LinearMap.range p :=
    e.ofSubmodules (LinearMap.range p'.hom) (LinearMap.range p) <| by
      rw [← LinearMap.range_comp, freeEquivPi_comp_hom_piEndToFree, LinearMap.range_comp,
        e.range, Submodule.map_top]
  refine ⟨n, b'.map eRange, d, fun i j => ?_⟩
  rw [Module.Basis.map_apply, LinearEquiv.ofSubmodules_apply, freeEquivPi_apply]
  have h := (mem_free_piece_iff 𝒜 (s ∘ eI.symm) (d i) (b' i).val).mp (hb' i) (eI j)
  simpa only [Function.comp_apply, Equiv.symm_apply_apply] using h

/-- Coordinate-space form of `exists_free_factorization_of_idempotent` on `I → A`: a degree-zero
idempotent `p` on `I → A` splits through `Fin n → A` via degree-zero maps `ι` and `π` with
`π ∘ₗ ι = id` and `ι ∘ₗ π = p`. -/
theorem exists_factorization_idempotent_pi [Module.IsTorsionFree k (𝒜 0)]
    (hneg : ∀ i < 0, 𝒜 i = ⊥) (hzero : ∀ a ∈ 𝒜 0, ∃ c : k, algebraMap k A c = a)
    {I : Type uI} [Finite I] (s : I → ℤ) (p : (I → A) →ₗ[A] (I → A)) (hp : p.comp p = p)
    (hhom : ∀ (d : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (d - s j)) → ∀ j, p v j ∈ 𝒜 (d - s j)) :
    ∃ (n : ℕ) (d : Fin n → ℤ) (ι : (Fin n → A) →ₗ[A] (I → A)) (π : (I → A) →ₗ[A] (Fin n → A)),
      π.comp ι = LinearMap.id ∧ ι.comp π = p ∧
        (∀ (q : ℤ) (v : Fin n → A), (∀ i, v i ∈ 𝒜 (q - d i)) → ∀ j, ι v j ∈ 𝒜 (q - s j)) ∧
        (∀ (q : ℤ) (v : I → A), (∀ j, v j ∈ 𝒜 (q - s j)) → ∀ i, π v i ∈ 𝒜 (q - d i)) := by
  classical
  cases nonempty_fintype I
  let eI : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  let es : free 𝒜 (s ∘ eI.symm) ≃ₗ[A] (I → A) := freeEquivPi (𝒜 := 𝒜) eI s
  let p' := piEndToFree (𝒜 := 𝒜) eI s p hhom
  obtain ⟨n, d, ι', π', hιπ', hπι'⟩ := exists_free_factorization_of_idempotent hneg hzero p'
    (piEndToFree_idempotent eI s p hp hhom)
  let ed : free 𝒜 d ≃ₗ[A] (Fin n → A) := DirectSum.linearEquivFunOnFintype A (Fin n) (fun _ => A)
  have hed_symm (v : Fin n → A) (i : Fin n) : (ed.symm v) i = v i :=
    congrFun (ed.apply_symm_apply v) i
  let ι : (Fin n → A) →ₗ[A] (I → A) := es.toLinearMap.comp (ι'.hom.comp ed.symm.toLinearMap)
  let π : (I → A) →ₗ[A] (Fin n → A) := ed.toLinearMap.comp (π'.hom.comp es.symm.toLinearMap)
  refine ⟨n, d, ι, π, ?_, ?_, ?_, ?_⟩
  · refine LinearMap.ext fun v => funext fun i => ?_
    have h := congrArg (fun x => x i) (LinearMap.congr_fun (congrArg Hom.hom hιπ') (ed.symm v))
    simp only [ι, π, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap, LinearMap.id_apply,
      LinearEquiv.symm_apply_apply]
    exact h.trans (hed_symm v i)
  · refine LinearMap.ext fun v => funext fun j => ?_
    have h := congrArg (fun x => x (eI j)) (LinearMap.congr_fun (congrArg Hom.hom hπι') (es.symm v))
    simp only [ι, π, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.symm_apply_apply]
    rw [freeEquivPi_apply]
    refine h.trans ?_
    rw [← freeEquivPi_apply (𝒜 := 𝒜) eI s (p'.hom (es.symm v)) j,
      freeEquivPi_piEndToFree, es.apply_symm_apply]
  · intro q v hv j
    have hv' : ed.symm v ∈ (free 𝒜 d).grading.piece q :=
      (mem_free_piece_iff 𝒜 d q (ed.symm v)).mpr fun i => by rw [hed_symm]; exact hv i
    have h := (mem_free_piece_iff 𝒜 (s ∘ eI.symm) q (ι'.hom (ed.symm v))).mp (map_mem ι' hv') (eI j)
    have hι : ι v j = (ι'.hom (ed.symm v)) (eI j) := by
      simp only [ι, LinearMap.comp_apply, LinearEquiv.coe_toLinearMap]
      exact freeEquivPi_apply eI s (ι'.hom (ed.symm v)) j
    rw [hι]
    simpa only [Function.comp_apply, Equiv.symm_apply_apply] using h
  · intro q v hv i
    have hv' : es.symm v ∈ (free 𝒜 (s ∘ eI.symm)).grading.piece q :=
      (mem_free_piece_iff 𝒜 (s ∘ eI.symm) q (es.symm v)).mpr fun t => by
        rw [freeEquivPi_symm_apply]
        exact hv (eI.symm t)
    exact (mem_free_piece_iff 𝒜 d q (π'.hom (es.symm v))).mp (map_mem π' hv') i

end PIDRetract

end TauCeti.GradedModuleCat
