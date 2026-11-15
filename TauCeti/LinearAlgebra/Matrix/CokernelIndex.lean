/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Group.Subgroup.Index
public import TauCeti.LinearAlgebra.FreeModule.CardQuotient
public import TauCeti.RingTheory.Ideal.Quotient.Pi
public import TauCeti.RingTheory.Ideal.Quotient.Regular
public import TauCeti.RingTheory.Subring.FiniteIndex
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.LinearAlgebra.Matrix.Nondegenerate
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.Data.ZMod.QuotientRing

/-!
# Cokernels of square matrices: finite ideals, finite-index subrings, and orders

Let `A` be a square matrix over a commutative ring. This file establishes comparisons for the
cokernel `(ι → R) ⧸ LinearMap.range A.mulVecLin` and assembles them to compute its cardinality over
finite-index subrings of finite products of principal ideal domains:

1. **Reduction modulo a finite ideal.** If `I` is an ideal of `R` whose underlying set is finite and
   `A.det ∈ nonZeroDivisors R`, then `A.mulVecLin` restricts to a bijection on the finite submodule
   `I^ι`, so `I^ι ≤ LinearMap.range A.mulVecLin` (`Matrix.piIdeal_le_range_mulVecLin_of_finite`) and
   reducing modulo `I` induces an `R`-linear isomorphism between `(ι → R) ⧸ range A.mulVecLin` and
   `(ι → R ⧸ I) ⧸ range (A.map (Ideal.Quotient.mk I)).mulVecLin`
   (`Matrix.cokernelQuotientEquivOfFinite`). Finiteness of `I` itself (not merely of `R ⧸ I`) is
   necessary, as witnessed at the end of the file for `R = ℤ`, `I = 2ℤ`, and `A = !![4]`.

2. **Passage to a finite-index subring.** If `S` is a subring of finite additive index in `R` and
   `A : Matrix ι ι S` has `(A.det : R) ∈ nonZeroDivisors R`, then `(A.map S.subtype).mulVecLin` is
   an injective additive endomorphism of `ι → R` stabilizing the finite-index subgroup `S^ι`, so the
   cokernels over `S` and over `R` have the same `Nat.card`
   (`Matrix.card_quotient_range_mulVecLin_subring`).

3. **Products and finite-index orders.** Over a product `∏ k, R k`, the cokernel decomposes
   coordinatewise (`Matrix.cokernelPiLinearEquiv`). Combining (1)–(3) with
   `Subring.restrictInfiniteHom` and Smith normal form on each factor
   (`Matrix.card_quotient_range_mulVecLin_eq_card_quotient_span_det`) proves that for a finite-index
   subring `S` of a finite product of principal ideal domains and `A : Matrix ι ι S` with
   `A.det ∈ nonZeroDivisors S`, `(ι → S) ⧸ range A.mulVecLin` and `S ⧸ Ideal.span {A.det}` have the
   same `Nat.card` (`Matrix.card_quotient_range_mulVecLin_eq_card_quotient_span_det_of_subring_pi`).

## Main definitions and results

* `Matrix.piIdeal_le_range_mulVecLin_of_finite`, `Matrix.cokernelQuotientEquivOfFinite`,
  `Matrix.card_quotient_range_mulVecLin_map_mk_of_finite`: cokernel invariance modulo a finite
  ideal.
* `Matrix.cokernelMapRingEquiv`: additive equivalence of cokernels induced by a ring equivalence.
* `Matrix.finite_quotient_range_mulVecLin_subring_iff`,
  `Matrix.card_quotient_range_mulVecLin_subring`: cokernel comparison along a finite-index subring.
* `Matrix.cokernelPiLinearEquiv`: coordinatewise decomposition of a matrix cokernel over `∏ k, R k`.
* `Matrix.card_quotient_range_mulVecLin_eq_card_quotient_span_det_of_subring_pi`,
  `Matrix.finite_quotient_range_mulVecLin_iff_finite_quotient_span_det_of_subring_pi`: cokernel
  order over a finite-index subring of a finite product of PIDs.
-/

public section

namespace Matrix

section FiniteIdeal

variable {R ι : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
  (I : Ideal R) [Finite I]

/-- If `I` is a finite ideal of `R` and `A.det ∈ nonZeroDivisors R`, then `I^ι` is contained in the
image of `A.mulVecLin`: `A.mulVecLin` restricts to an injective self-map of the finite submodule
`I^ι`, hence a bijection. -/
theorem piIdeal_le_range_mulVecLin_of_finite {A : Matrix ι ι R}
    (hA : A.det ∈ nonZeroDivisors R) :
    Submodule.pi Set.univ (fun _ : ι ↦ I) ≤ LinearMap.range A.mulVecLin := by
  let P : Submodule R (ι → R) := Submodule.pi Set.univ fun _ : ι ↦ I
  have hPfin : Finite P :=
    Finite.of_injective (fun x : P ↦ fun i : ι ↦ (⟨x.1 i, x.2 i trivial⟩ : I))
      fun x y hxy ↦ Subtype.ext (funext fun i ↦ congrArg Subtype.val (congr_fun hxy i))
  have hmap (x : P) : A.mulVecLin x.1 ∈ P := fun i _ ↦ by
    simp only [mulVecLin_apply, mulVec, dotProduct]
    exact I.sum_mem fun j _ ↦ I.mul_mem_left (A i j) (x.2 j trivial)
  have hinj : Function.Injective (fun x : P ↦ (⟨A.mulVecLin x.1, hmap x⟩ : P)) :=
    fun x y hxy ↦ Subtype.ext <|
      mulVec_injective_of_det_mem_nonZeroDivisors hA (congrArg Subtype.val hxy)
  intro y hy
  obtain ⟨x, hx⟩ := Finite.surjective_of_injective hinj ⟨y, hy⟩
  exact ⟨x.1, congrArg Subtype.val hx⟩

/-- **Cokernel isomorphism modulo a finite ideal.** When `I : Ideal R` is finite and
`A.det ∈ nonZeroDivisors R`, reducing coordinates modulo `I` identifies the cokernel of `A` with the
cokernel of `A.map (Ideal.Quotient.mk I)`. -/
noncomputable def cokernelQuotientEquivOfFinite {A : Matrix ι ι R}
    (hA : A.det ∈ nonZeroDivisors R) :
    ((ι → R) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[R]
      ((ι → R ⧸ I) ⧸ LinearMap.range (A.map (Ideal.Quotient.mk I)).mulVecLin) := by
  let π : (ι → R) →ₗ[R] (ι → R ⧸ I) :=
    LinearMap.pi fun i ↦ (Ideal.Quotient.mkₐ R I).toLinearMap.comp (LinearMap.proj i)
  let q : (ι → R) →ₗ[R]
      ((ι → R ⧸ I) ⧸ LinearMap.range (A.map (Ideal.Quotient.mk I)).mulVecLin) :=
    ((LinearMap.range (A.map (Ideal.Quotient.mk I)).mulVecLin).mkQ.restrictScalars R).comp π
  have hπ_surj : Function.Surjective π :=
    Function.Surjective.piMap fun _ ↦ Ideal.Quotient.mk_surjective
  have hq_surj : Function.Surjective q :=
    (Submodule.mkQ_surjective _).comp hπ_surj
  have hcomm (v : ι → R) :
      π (A.mulVecLin v) = (A.map (Ideal.Quotient.mk I)).mulVecLin (π v) := by
    ext i
    simp [π, mulVec, dotProduct]
  have hker : LinearMap.range A.mulVecLin = LinearMap.ker q := by
    refine le_antisymm ?_ fun x hx ↦ ?_
    · rintro _ ⟨v, rfl⟩
      simp only [LinearMap.mem_ker, q, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, hcomm, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
      exact ⟨π v, rfl⟩
    · simp only [LinearMap.mem_ker, q, LinearMap.comp_apply, LinearMap.restrictScalars_apply,
        Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range] at hx
      obtain ⟨w, hw⟩ := hx
      obtain ⟨v, rfl⟩ := hπ_surj w
      have hmem : x - A.mulVecLin v ∈ Submodule.pi Set.univ (fun _ : ι ↦ I) := by
        intro i _
        have hi : Ideal.Quotient.mk I (x i - A.mulVecLin v i) = 0 := by
          have hsub : π (x - A.mulVecLin v) i = 0 := by
            rw [map_sub, hcomm, hw, sub_self, Pi.zero_apply]
          simpa [π] using hsub
        exact Ideal.Quotient.eq_zero_iff_mem.mp hi
      have hrange := piIdeal_le_range_mulVecLin_of_finite I hA hmem
      simpa using Submodule.add_mem _ hrange ⟨v, rfl⟩
  exact (Submodule.quotEquivOfEq _ _ hker).trans (q.quotKerEquivOfSurjective hq_surj)

/-- `cokernelQuotientEquivOfFinite` acts coordinatewise by `Ideal.Quotient.mk I` on representatives.
-/
@[simp]
theorem cokernelQuotientEquivOfFinite_mk {A : Matrix ι ι R} (hA : A.det ∈ nonZeroDivisors R)
    (v : ι → R) :
    cokernelQuotientEquivOfFinite I hA (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (fun i ↦ Ideal.Quotient.mk I (v i)) :=
  (rfl)

/-- The inverse of `cokernelQuotientEquivOfFinite` lifts `fun i ↦ mk I (v i)` to `mk v`. -/
@[simp]
theorem cokernelQuotientEquivOfFinite_symm_mk {A : Matrix ι ι R} (hA : A.det ∈ nonZeroDivisors R)
    (v : ι → R) :
    (cokernelQuotientEquivOfFinite I hA).symm
        (Submodule.Quotient.mk fun i ↦ Ideal.Quotient.mk I (v i)) =
      Submodule.Quotient.mk v :=
  (cokernelQuotientEquivOfFinite I hA).symm_apply_eq.mpr (rfl)

/-- If `I` is a finite ideal and `A.det ∈ nonZeroDivisors R`, the cokernel of
`A.map (Ideal.Quotient.mk I)` is finite if and only if the cokernel of `A` is finite. -/
theorem finite_quotient_range_mulVecLin_map_mk_iff_of_finite {A : Matrix ι ι R}
    (hA : A.det ∈ nonZeroDivisors R) :
    Finite ((ι → R ⧸ I) ⧸ LinearMap.range (A.map (Ideal.Quotient.mk I)).mulVecLin) ↔
      Finite ((ι → R) ⧸ LinearMap.range A.mulVecLin) :=
  (cokernelQuotientEquivOfFinite I hA).symm.toEquiv.finite_iff

/-- If `I` is a finite ideal and `A.det ∈ nonZeroDivisors R`, reducing `A` modulo `I` preserves the
`Nat.card` of its cokernel (`0` when infinite). -/
theorem card_quotient_range_mulVecLin_map_mk_of_finite {A : Matrix ι ι R}
    (hA : A.det ∈ nonZeroDivisors R) :
    Nat.card ((ι → R ⧸ I) ⧸ LinearMap.range (A.map (Ideal.Quotient.mk I)).mulVecLin) =
      Nat.card ((ι → R) ⧸ LinearMap.range A.mulVecLin) :=
  Nat.card_congr (cokernelQuotientEquivOfFinite I hA).symm.toEquiv

end FiniteIdeal

section RingEquiv

variable {R₁ R₂ ι : Type*} [CommRing R₁] [CommRing R₂] [Fintype ι]

/-- Transport of a square matrix cokernel along a ring isomorphism. -/
noncomputable def cokernelMapRingEquiv (e : R₁ ≃+* R₂) (A : Matrix ι ι R₁) :
    ((ι → R₁) ⧸ LinearMap.range A.mulVecLin) ≃+
      ((ι → R₂) ⧸ LinearMap.range (A.map e).mulVecLin) :=
  QuotientAddGroup.congr (LinearMap.range A.mulVecLin).toAddSubgroup
    (LinearMap.range (A.map e).mulVecLin).toAddSubgroup
    (AddEquiv.piCongrRight fun _ : ι ↦ e.toAddEquiv) <| by
      ext w
      simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.mem_range]
      refine ⟨?_, ?_⟩
      · rintro ⟨x, ⟨u, rfl⟩, rfl⟩
        refine ⟨fun i ↦ e (u i), funext fun i ↦ ?_⟩
        simp [mulVec, dotProduct]
      · rintro ⟨u, rfl⟩
        refine ⟨A.mulVecLin fun i ↦ e.symm (u i), ⟨_, rfl⟩, funext fun i ↦ ?_⟩
        simp [mulVec, dotProduct]

/-- `cokernelMapRingEquiv e A` acts coordinatewise by `e` on representatives. -/
@[simp]
theorem cokernelMapRingEquiv_mk (e : R₁ ≃+* R₂) (A : Matrix ι ι R₁) (v : ι → R₁) :
    cokernelMapRingEquiv e A (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (fun i ↦ e (v i)) :=
  (rfl)

/-- `(cokernelMapRingEquiv e A).symm` acts coordinatewise by `e.symm` on representatives. -/
@[simp]
theorem cokernelMapRingEquiv_symm_mk (e : R₁ ≃+* R₂) (A : Matrix ι ι R₁) (v : ι → R₂) :
    (cokernelMapRingEquiv e A).symm (Submodule.Quotient.mk v) =
      Submodule.Quotient.mk (fun i ↦ e.symm (v i)) :=
  (rfl)

end RingEquiv

section Subring

variable {R ι : Type*} [CommRing R] [Fintype ι]
  {S : Subring R} [S.toAddSubgroup.FiniteIndex]

private def piSubringAddEquiv (S : Subring R) :
    (ι → S) ≃+ AddSubgroup.pi Set.univ (fun _ : ι ↦ S.toAddSubgroup) where
  toFun v := ⟨fun i ↦ (v i : R), fun i _ ↦ (v i).2⟩
  invFun w i := ⟨w.1 i, w.2 i trivial⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl

private noncomputable def cokernelSubringEquivQuotientRange (S : Subring R) (A : Matrix ι ι S) :
    ((ι → S) ⧸ LinearMap.range A.mulVecLin) ≃+
      (AddSubgroup.pi Set.univ (fun _ : ι ↦ S.toAddSubgroup) ⧸
        ((piSubringAddEquiv S).toAddMonoidHom.comp
          (A.mulVecLin.toAddMonoidHom.comp (piSubringAddEquiv S).symm.toAddMonoidHom)).range) :=
  QuotientAddGroup.congr (LinearMap.range A.mulVecLin).toAddSubgroup _ (piSubringAddEquiv S) <| by
    ext w
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, LinearMap.mem_range,
      AddMonoidHom.mem_range, AddMonoidHom.coe_comp, Function.comp_apply,
      AddEquiv.coe_toAddMonoidHom, LinearMap.toAddMonoidHom_coe]
    refine ⟨?_, ?_⟩
    · rintro ⟨x, ⟨v, rfl⟩, rfl⟩
      exact ⟨piSubringAddEquiv S v, by simp⟩
    · rintro ⟨u, rfl⟩
      exact ⟨A.mulVecLin ((piSubringAddEquiv S).symm u), ⟨_, rfl⟩, rfl⟩

/-- **Cokernel cardinality along a finite-index subring.** If `S` has finite additive index in `R`
and `(A.det : R) ∈ nonZeroDivisors R`, then `(ι → S) ⧸ range A.mulVecLin` and
`(ι → R) ⧸ range (A.map S.subtype).mulVecLin` have the same `Nat.card` (`0` when infinite). -/
theorem card_quotient_range_mulVecLin_subring [DecidableEq ι] {A : Matrix ι ι S}
    (hA : (A.det : R) ∈ nonZeroDivisors R) :
    Nat.card ((ι → S) ⧸ LinearMap.range A.mulVecLin) =
      Nat.card ((ι → R) ⧸ LinearMap.range (A.map S.subtype).mulVecLin) := by
  let H : AddSubgroup (ι → R) := AddSubgroup.pi Set.univ fun _ : ι ↦ S.toAddSubgroup
  let g : H →+ H := (piSubringAddEquiv S).toAddMonoidHom.comp
    (A.mulVecLin.toAddMonoidHom.comp (piSubringAddEquiv S).symm.toAddMonoidHom)
  let f : (ι → R) →+ (ι → R) := (A.map S.subtype).mulVecLin.toAddMonoidHom
  have hdet : (A.map S.subtype).det ∈ nonZeroDivisors R := by
    rwa [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  have hinj : Function.Injective f := mulVec_injective_of_det_mem_nonZeroDivisors hdet
  have hcomp : f.comp H.subtype = H.subtype.comp g := by
    ext w i
    simp [f, g, piSubringAddEquiv, mulVec, dotProduct]
  rw [Nat.card_congr (cokernelSubringEquivQuotientRange S A).toEquiv,
    AddSubgroup.natCard_quotient_range_eq_of_comp_subtype (H := H) hinj hcomp]
  rfl

/-- If `S` has finite additive index in `R` and `(A.det : R) ∈ nonZeroDivisors R`, the cokernel of
`A` over `S` is finite if and only if the cokernel of `A.map S.subtype` over `R` is finite. -/
theorem finite_quotient_range_mulVecLin_subring_iff [DecidableEq ι] {A : Matrix ι ι S}
    (hA : (A.det : R) ∈ nonZeroDivisors R) :
    Finite ((ι → S) ⧸ LinearMap.range A.mulVecLin) ↔
      Finite ((ι → R) ⧸ LinearMap.range (A.map S.subtype).mulVecLin) := by
  have h1 : Nonempty ((ι → S) ⧸ LinearMap.range A.mulVecLin) := ⟨0⟩
  have h2 : Nonempty ((ι → R) ⧸ LinearMap.range (A.map S.subtype).mulVecLin) := ⟨0⟩
  exact (and_iff_right h1).symm.trans <| Nat.card_ne_zero.symm.trans <|
    (eq_iff_iff.mp (congrArg (· ≠ 0) (card_quotient_range_mulVecLin_subring hA))).trans <|
      Nat.card_ne_zero.trans (and_iff_right h2)

end Subring

section Pi

variable {κ ι : Type*} {R : κ → Type*} [∀ k, CommRing (R k)] [Fintype ι]

/-- Over a product of commutative rings `∏ k, R k`, the cokernel of a square matrix `A` decomposes
as the product of the cokernels of its projections `A.map (Pi.evalRingHom R k)`. Neither
`[DecidableEq ι]` nor finiteness of `κ` is needed. -/
noncomputable def cokernelPiLinearEquiv (A : Matrix ι ι (∀ k, R k)) :
    ((ι → ∀ k, R k) ⧸ LinearMap.range A.mulVecLin) ≃ₗ[∀ k, R k]
      ∀ k, ((ι → R k) ⧸ LinearMap.range (A.map (Pi.evalRingHom R k)).mulVecLin) := by
  let φ : (ι → ∀ k, R k) →ₗ[∀ k, R k]
      ∀ k, ((ι → R k) ⧸ LinearMap.range (A.map (Pi.evalRingHom R k)).mulVecLin) :=
    { toFun := fun v k ↦ Submodule.Quotient.mk fun i ↦ v i k
      map_add' := fun u v ↦ funext fun k ↦ by
        simp only [Pi.add_apply, ← Submodule.Quotient.mk_add]
        rfl
      map_smul' := fun c v ↦ funext fun k ↦ by
        simp only [RingHom.id_apply, Pi.smul_apply]
        rfl }
  have hsurj : Function.Surjective φ := fun y ↦
    ⟨fun i k ↦ Quotient.out (y k) i, funext fun k ↦ Quotient.out_eq' (y k)⟩
  have hker : LinearMap.range A.mulVecLin = LinearMap.ker φ := by
    ext v
    simp only [LinearMap.mem_range, LinearMap.mem_ker, φ, LinearMap.coe_mk, AddHom.coe_mk]
    refine ⟨?_, fun h ↦ ?_⟩
    · rintro ⟨u, rfl⟩
      ext k
      rw [Pi.zero_apply, Submodule.Quotient.mk_eq_zero, LinearMap.mem_range]
      refine ⟨fun i ↦ u i k, funext fun i ↦ ?_⟩
      simp [mulVec, dotProduct]
    · have hmem (k : κ) : (fun i ↦ v i k) ∈
          LinearMap.range (A.map (Pi.evalRingHom R k)).mulVecLin := by
        simpa [Submodule.Quotient.mk_eq_zero] using congr_fun h k
      choose u hu using hmem
      refine ⟨fun i k ↦ u k i, funext fun i ↦ funext fun k ↦ ?_⟩
      have hik := congr_fun (hu k) i
      simpa [mulVec, dotProduct] using hik
  exact (Submodule.quotEquivOfEq _ _ hker).trans (φ.quotKerEquivOfSurjective hsurj)

/-- Evaluating `cokernelPiLinearEquiv A` on `mk v` at factor `k` gives `mk (fun i ↦ v i k)`. -/
@[simp]
theorem cokernelPiLinearEquiv_mk (A : Matrix ι ι (∀ k, R k)) (v : ι → ∀ k, R k) (k : κ) :
    cokernelPiLinearEquiv A (Submodule.Quotient.mk v) k =
      Submodule.Quotient.mk (fun i ↦ v i k) :=
  (rfl)

/-- `(cokernelPiLinearEquiv A).symm` assembles factorwise classes `mk (v k)` into
`mk (fun i k ↦ v k i)`. -/
@[simp]
theorem cokernelPiLinearEquiv_symm_mk (A : Matrix ι ι (∀ k, R k)) (v : ∀ k, ι → R k) :
    (cokernelPiLinearEquiv A).symm (fun k ↦ Submodule.Quotient.mk (v k)) =
      Submodule.Quotient.mk (fun i k ↦ v k i) :=
  (cokernelPiLinearEquiv A).symm_apply_eq.mpr (rfl)

end Pi

section SubringPiPID

variable {κ ι : Type*} [Finite κ] {D : κ → Type*}
  [∀ k, CommRing (D k)] [∀ k, IsDomain (D k)] [∀ k, IsPrincipalIdealRing (D k)]
  [Fintype ι] [DecidableEq ι]

/-- Helper case where every factor `D k` is already an infinite principal ideal domain. -/
private theorem card_quotient_range_mulVecLin_eq_of_infinite_pid [∀ k, Infinite (D k)]
    {S : Subring (∀ k, D k)} [S.toAddSubgroup.FiniteIndex]
    {A : Matrix ι ι S} (hA : A.det ∈ nonZeroDivisors S) :
    Nat.card ((ι → S) ⧸ LinearMap.range A.mulVecLin) =
      Nat.card (S ⧸ Ideal.span {A.det}) := by
  let _ : Fintype κ := Fintype.ofFinite κ
  have hdet_coe : (A.det : ∀ k, D k) ∈ nonZeroDivisors (∀ k, D k) :=
    S.coe_mem_nonZeroDivisors_iff.mpr hA
  have hdet_ne : ∀ k, (A.det : ∀ k, D k) k ≠ 0 :=
    (S.mem_nonZeroDivisors_iff_forall_ne_zero).mp hA
  calc Nat.card ((ι → S) ⧸ LinearMap.range A.mulVecLin)
      = Nat.card ((ι → ∀ k, D k) ⧸ LinearMap.range (A.map S.subtype).mulVecLin) :=
        card_quotient_range_mulVecLin_subring hdet_coe
    _ = ∏ k, Nat.card ((ι → D k) ⧸
          LinearMap.range ((A.map S.subtype).map (Pi.evalRingHom D k)).mulVecLin) := by
        rw [Nat.card_congr (cokernelPiLinearEquiv (A.map S.subtype)).toEquiv, Nat.card_pi]
    _ = ∏ k, Nat.card (D k ⧸ Ideal.span {(A.det : ∀ k, D k) k}) := by
        refine Finset.prod_congr rfl fun k _ ↦ ?_
        have hk : ((A.map S.subtype).map (Pi.evalRingHom D k)).det = (A.det : ∀ k, D k) k := by
          rw [← RingHom.mapMatrix_apply, ← RingHom.map_det,
            ← RingHom.mapMatrix_apply, ← RingHom.map_det]
          rfl
        rw [card_quotient_range_mulVecLin_eq_card_quotient_span_det (hk ▸ hdet_ne k), hk]
    _ = Nat.card ((∀ k, D k) ⧸ Ideal.span {(A.det : ∀ k, D k)}) := by
        rw [← Nat.card_pi,
          Nat.card_congr (Ideal.quotientSpanSingletonPiEquiv (A.det : ∀ k, D k)).toEquiv]
    _ = Nat.card (S ⧸ Ideal.span {A.det}) :=
        (S.natCard_quotient_span_singleton hdet_coe).symm

/-- **Cokernel order over a finite-index subring of a finite product of principal ideal domains.**
If `S` has finite additive index in `∏ k, D k` (each `D k` a principal ideal domain, finite or
infinite) and `A : Matrix ι ι S` has `A.det ∈ nonZeroDivisors S`, then
`(ι → S) ⧸ LinearMap.range A.mulVecLin` and `S ⧸ Ideal.span {A.det}` have the same `Nat.card`
(`0` when infinite). -/
theorem card_quotient_range_mulVecLin_eq_card_quotient_span_det_of_subring_pi
    {S : Subring (∀ k, D k)} [S.toAddSubgroup.FiniteIndex]
    {A : Matrix ι ι S} (hA : A.det ∈ nonZeroDivisors S) :
    Nat.card ((ι → S) ⧸ LinearMap.range A.mulVecLin) =
      Nat.card (S ⧸ Ideal.span {A.det}) := by
  let φ := S.restrictInfiniteHom
  let K : Ideal S := RingHom.ker φ
  let e : S ⧸ K ≃+* φ.range := RingHom.quotientKerEquivRange φ
  have hmk_det : Ideal.Quotient.mk K A.det ∈ nonZeroDivisors (S ⧸ K) :=
    Ideal.Quotient.mk_mem_nonZeroDivisors_of_finite K hA
  have hAbar_det : (A.map (Ideal.Quotient.mk K)).det = Ideal.Quotient.mk K A.det := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
  let A' : Matrix ι ι φ.range := (A.map (Ideal.Quotient.mk K)).map e.toRingHom
  have hA'_det_eq : A'.det = e (Ideal.Quotient.mk K A.det) := by
    dsimp only [A']
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det, hAbar_det]
    rfl
  have hA'_det : A'.det ∈ nonZeroDivisors φ.range := by
    rw [hA'_det_eq, mem_nonZeroDivisors_iff_left]
    intro y hy
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, map_eq_zero_iff e e.injective] at hy
    rw [mem_nonZeroDivisors_iff_left.mp hmk_det z hy, map_zero]
  have hspan_equiv : ((S ⧸ K) ⧸ Ideal.span {Ideal.Quotient.mk K A.det}) ≃+*
      (φ.range ⧸ Ideal.span {A'.det}) :=
    Ideal.quotientEquiv _ _ e (by simp [Ideal.map_span, hA'_det_eq])
  have (k : {i : κ // Infinite (D i)}) : Infinite (D k.1) := k.2
  calc Nat.card ((ι → S) ⧸ LinearMap.range A.mulVecLin)
      = Nat.card ((ι → S ⧸ K) ⧸ LinearMap.range (A.map (Ideal.Quotient.mk K)).mulVecLin) :=
        (card_quotient_range_mulVecLin_map_mk_of_finite K hA).symm
    _ = Nat.card ((ι → φ.range) ⧸ LinearMap.range A'.mulVecLin) :=
        Nat.card_congr (cokernelMapRingEquiv e (A.map (Ideal.Quotient.mk K))).toEquiv
    _ = Nat.card (φ.range ⧸ Ideal.span {A'.det}) :=
        card_quotient_range_mulVecLin_eq_of_infinite_pid hA'_det
    _ = Nat.card ((S ⧸ K) ⧸ Ideal.span {Ideal.Quotient.mk K A.det}) :=
        Nat.card_congr hspan_equiv.symm.toEquiv
    _ = Nat.card (S ⧸ Ideal.span {A.det}) :=
        Nat.card_congr (K.quotientSpanSingletonQuotientEquivOfFinite hA).toEquiv

/-- Under the hypotheses of `card_quotient_range_mulVecLin_eq_card_quotient_span_det_of_subring_pi`,
the cokernel of `A` is finite if and only if `S ⧸ Ideal.span {A.det}` is finite. -/
theorem finite_quotient_range_mulVecLin_iff_finite_quotient_span_det_of_subring_pi
    {S : Subring (∀ k, D k)} [S.toAddSubgroup.FiniteIndex]
    {A : Matrix ι ι S} (hA : A.det ∈ nonZeroDivisors S) :
    Finite ((ι → S) ⧸ LinearMap.range A.mulVecLin) ↔
      Finite (S ⧸ Ideal.span {A.det}) := by
  have h1 : Nonempty ((ι → S) ⧸ LinearMap.range A.mulVecLin) := ⟨0⟩
  have h2 : Nonempty (S ⧸ Ideal.span {A.det}) := ⟨0⟩
  have hcard := card_quotient_range_mulVecLin_eq_card_quotient_span_det_of_subring_pi hA
  simpa [Nat.card_ne_zero, h1, h2] using congrArg (· ≠ 0) hcard

end SubringPiPID

end Matrix

section Counterexample

-- Finiteness of `I` itself is required in `Matrix.card_quotient_range_mulVecLin_map_mk_of_finite`:
-- for `R = ℤ`, `I = 2ℤ` (`ℤ ⧸ I` has size `2`), and `A = !![4]`, `A.det = 4 ∈ ℤ⁰`, yet the
-- cokernel of `A` has size `4` while the cokernel of `A.map (Ideal.Quotient.mk I) = !![0]` has
-- size `2`.
example :
    let I : Ideal ℤ := Ideal.span {((2 : ℕ) : ℤ)}
    let A : Matrix (Fin 1) (Fin 1) ℤ := !![(4 : ℤ)]
    A.det ∈ nonZeroDivisors ℤ ∧
      Finite (ℤ ⧸ I) ∧
      Nat.card ((Fin 1 → ℤ ⧸ I) ⧸ LinearMap.range (A.map (Ideal.Quotient.mk I)).mulVecLin) ≠
        Nat.card ((Fin 1 → ℤ) ⧸ LinearMap.range A.mulVecLin) := by
  intro I A
  have hdet : A.det ∈ nonZeroDivisors ℤ := by
    rw [Matrix.det_fin_one]
    exact mem_nonZeroDivisors_of_ne_zero (by decide)
  have hfin : Finite (ℤ ⧸ I) :=
    Finite.of_equiv (ZMod 2) (Int.quotientSpanNatEquivZMod 2).toEquiv.symm
  refine ⟨hdet, hfin, ?_⟩
  have hA0 : A.map (Ideal.Quotient.mk I) = 0 := by
    ext i j
    fin_cases i
    fin_cases j
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨2, rfl⟩)
  have hmap0 : (A.map (Ideal.Quotient.mk I)).mulVecLin = 0 :=
    LinearMap.ext fun v ↦ by simp [hA0]
  have hcard_quot :
      Nat.card ((Fin 1 → ℤ ⧸ I) ⧸ LinearMap.range (A.map (Ideal.Quotient.mk I)).mulVecLin) = 2 := by
    rw [hmap0, LinearMap.range_zero]
    have e1 : ((Fin 1 → ℤ ⧸ I) ⧸ (⊥ : Submodule (ℤ ⧸ I) (Fin 1 → ℤ ⧸ I))) ≃ (ℤ ⧸ I) :=
      (Submodule.quotEquivOfEqBot _ rfl).toEquiv.trans (Equiv.funUnique (Fin 1) (ℤ ⧸ I))
    rw [Nat.card_congr e1, Nat.card_congr (Int.quotientSpanNatEquivZMod 2).toEquiv, Nat.card_zmod]
  have hcard_int : Nat.card ((Fin 1 → ℤ) ⧸ LinearMap.range A.mulVecLin) = 4 := by
    let φ : (Fin 1 → ℤ) →ₗ[ℤ] (ℤ ⧸ Ideal.span {((4 : ℕ) : ℤ)}) :=
      (Ideal.span {((4 : ℕ) : ℤ)}).mkQ.comp (LinearMap.proj 0)
    have hsurj : Function.Surjective φ :=
      (Submodule.mkQ_surjective _).comp fun z ↦ ⟨fun _ ↦ z, rfl⟩
    have hker : LinearMap.range A.mulVecLin = LinearMap.ker φ := by
      ext v
      simp only [LinearMap.mem_range, LinearMap.mem_ker, φ, LinearMap.comp_apply,
        LinearMap.coe_proj, Function.eval, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        Ideal.mem_span_singleton]
      refine ⟨?_, ?_⟩
      · rintro ⟨u, rfl⟩
        exact ⟨u 0, by simp [A, Matrix.mulVec, dotProduct]⟩
      · rintro ⟨k, hk⟩
        refine ⟨fun _ ↦ k, funext fun i ↦ ?_⟩
        fin_cases i
        simp [A, Matrix.mulVec, dotProduct, hk]
    have e1 : ((Fin 1 → ℤ) ⧸ LinearMap.range A.mulVecLin) ≃ (ℤ ⧸ Ideal.span {((4 : ℕ) : ℤ)}) :=
      ((Submodule.quotEquivOfEq _ _ hker).trans (φ.quotKerEquivOfSurjective hsurj)).toEquiv
    rw [Nat.card_congr e1, Nat.card_congr (Int.quotientSpanNatEquivZMod 4).toEquiv, Nat.card_zmod]
  rw [hcard_quot, hcard_int]
  decide

end Counterexample
