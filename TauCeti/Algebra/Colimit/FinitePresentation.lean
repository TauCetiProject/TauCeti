/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Colimit.DirectLimit
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.Data.Finset.Order

/-!
# Algebra maps from finitely presented algebras into directed colimits

Let `B i` be a directed system of `A`-algebras, indexed by a nonempty directed preorder, with
`A`-algebra transition maps `f i j`, and let `DirectLimit B f` be its colimit, an `A`-algebra.
This file shows that `Hom_A(S, -)` commutes with this colimit when `S` is finitely presented:

* an `A`-algebra map from a finitely presented `S` into the colimit factors through some stage;
* two `A`-algebra maps from an `A`-algebra `S` of finite type into a stage that agree in the
  colimit already agree at a later stage.

It also shows that base change commutes with directed colimits of algebras:
`(colim B i) ⊗[A] M ≃ₐ[A] colim (B i ⊗[A] M)`. Combining the two, maps from a finitely presented
`A`-algebra `S` into `(colim B i) ⊗[A] M` descend to some `B i ⊗[A] M`, uniquely up to passing to
a later stage. In base change form, every `R`-algebra map `R ⊗[A] S → R ⊗[A] M`, for
`R = colim B i`, is the base change of a `B i`-algebra map `B i ⊗[A] S → B i ⊗[A] M`, and two such
maps with the same base change agree at a later stage. For `S` and `M` finite étale this is the
full faithfulness half of the statement that finite étale algebras over a directed colimit of
rings are the directed 2-colimit of finite étale algebras over the stages.

Mathlib proves the first two statements for colimit cocones in `Under R` over `CommRingCat`
(`RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit` and
`RingHom.EssFiniteType.exists_comp_map_eq_of_isColimit`, in
`Mathlib/Algebra/Category/Ring/FinitePresentation.lean`); the proofs here follow the same plan for
the concrete colimit `DirectLimit` of a directed system of algebras.

## Main results

* `DirectLimit.Algebra.exists_eq_comp_of_finitePresentation`: an `A`-algebra map from a finitely
  presented `A`-algebra into a directed colimit of `A`-algebras factors through some stage.
* `DirectLimit.Algebra.exists_comp_eq_comp_of_finiteType`: two `A`-algebra maps from an
  `A`-algebra of finite type into a stage which agree in the colimit agree at a later stage.
* `Algebra.TensorProduct.directLimitLeft`: `(colim B i) ⊗[A] M ≃ₐ[A] colim (B i ⊗[A] M)`.
* `DirectLimit.Algebra.exists_comp_rTensor_eq_rTensor_comp`,
  `DirectLimit.Algebra.exists_rTensor_comp_eq_rTensor_comp`: descent and eventual equality of
  maps between base changes `R ⊗[A] S → R ⊗[A] M`, for `S` finitely presented.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Remark 1.2.9.
-/

public section

open TensorProduct

section CommSemiring

variable {A ι : Type*} [CommSemiring A] [Preorder ι] {B : ι → Type*} [∀ i, CommSemiring (B i)]
  [∀ i, Algebra A (B i)] {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]
  {S : Type*} [Semiring S] [Algebra A S] (M : Type*) [CommSemiring M] [Algebra A M]

/-- Base change along a fixed `A`-algebra `M` turns a directed system of `A`-algebras `B i` into
the directed system of `A`-algebras `B i ⊗[A] M`. -/
instance DirectedSystem.algebraRTensor :
    DirectedSystem (B · ⊗[A] M) fun i j h ↦ Algebra.TensorProduct.rTensor M (f i j h) where
  map_self i x := by
    induction x using TensorProduct.inductionOn with
    | tmul b m => simp [DirectedSystem.map_self' f]
    | add x y hx hy => simp_all
  map_map := by
    intro k j i hij hjk x
    induction x using TensorProduct.inductionOn with
    | tmul b m => simp [DirectedSystem.map_map' f]
    | add x y hx hy => simp_all

namespace DirectLimit.Algebra

variable [IsDirectedOrder ι] [Nonempty ι]

/-- The canonical maps into a direct limit of algebras are compatible with the transition
maps. -/
@[simp]
theorem of_comp_f {i j : ι} (hij : i ≤ j) : (of B f j).comp (f i j hij) = of B f i :=
  AlgHom.ext fun _ ↦ of_f _ _

/-- Two `A`-algebra maps from an `A`-algebra of finite type into a stage of a directed colimit of
`A`-algebras which agree in the colimit already agree at a later stage. -/
theorem exists_comp_eq_comp_of_finiteType [Algebra.FiniteType A S] {j : ι}
    {ψ₁ ψ₂ : S →ₐ[A] B j} (h : (of B f j).comp ψ₁ = (of B f j).comp ψ₂) :
    ∃ k, ∃ hjk : j ≤ k, (f j k hjk).comp ψ₁ = (f j k hjk).comp ψ₂ := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A S).FG)
  -- Each of the finitely many generators is equalized at some later stage.
  have hgen (x : s) : ∃ k, ∃ hjk : j ≤ k, f j k hjk (ψ₁ x) = f j k hjk (ψ₂ x) := by
    obtain ⟨k, hk₁, hk₂, hk⟩ := Quotient.eq.mp congr($h x)
    exact ⟨k, hk₁, hk⟩
  choose k hjk hk using hgen
  obtain ⟨l, hl⟩ := Finset.exists_le (insert j (Finset.univ.image k))
  have hjl : j ≤ l := hl j (Finset.mem_insert_self _ _)
  have hkl (x : s) : k x ≤ l :=
    hl _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  refine ⟨l, hjl, AlgHom.ext_of_adjoin_eq_top hs fun x hx ↦ ?_⟩
  simp only [AlgHom.comp_apply]
  rw [← DirectedSystem.map_map' f (hjk ⟨x, hx⟩) (hkl ⟨x, hx⟩), hk]
  exact DirectedSystem.map_map' f _ _ _

end DirectLimit.Algebra

namespace Algebra.TensorProduct

variable [IsDirectedOrder ι] [Nonempty ι]

open DirectLimit.Algebra

/-- The map `colim (B i ⊗[A] M) → (colim B i) ⊗[A] M` induced by the base changes of the
canonical maps `B i → colim B i`. -/
private noncomputable def fromDirectLimit :
    DirectLimit (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) →ₐ[A] DirectLimit B f ⊗[A] M :=
  DirectLimit.Algebra.lift _ _ _ (fun i ↦ rTensor M (of B f i)) fun i j hij x ↦ by
    rw [← AlgHom.comp_apply, ← map_comp, of_comp_f, AlgHom.comp_id]

/-- The map `(colim B i) ⊗[A] M → colim (B i ⊗[A] M)`, sending `[b] ⊗ m` to `[b ⊗ m]`. -/
private noncomputable def toDirectLimit :
    DirectLimit B f ⊗[A] M →ₐ[A] DirectLimit (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) :=
  lift (DirectLimit.Algebra.lift _ _ _
      (fun i ↦ (of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) i).comp includeLeft)
      fun i j hij b ↦ by
        simp only [AlgHom.comp_apply, includeLeft_apply]
        rw [← of_f (G := (B · ⊗[A] M)) (f := fun i j h ↦ rTensor M (f i j h)) hij]
        simp only [map_tmul, AlgHom.id_apply])
    ((of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) (Classical.arbitrary ι)).comp includeRight)
    fun _ _ ↦ .all _ _

private theorem fromDirectLimit_of (i : ι) (x : B i ⊗[A] M) :
    fromDirectLimit M (of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) i x) =
      rTensor M (of B f i) x :=
  DirectLimit.Algebra.lift_of ..

private theorem toDirectLimit_of_tmul (i : ι) (b : B i) (m : M) :
    toDirectLimit M (of B f i b ⊗ₜ m) =
      of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) i (b ⊗ₜ m) := by
  -- The image of `1 ⊗ m` does not depend on the stage it is taken at.
  have h1 (j : ι) : of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) j (1 ⊗ₜ m) =
      of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) i (1 ⊗ₜ m) := by
    obtain ⟨k, hjk, hik⟩ := exists_ge_ge j i
    rw [← of_f (G := (B · ⊗[A] M)) (f := fun i j h ↦ rTensor M (f i j h)) hjk,
      ← of_f (G := (B · ⊗[A] M)) (f := fun i j h ↦ rTensor M (f i j h)) hik]
    simp only [map_tmul, map_one, AlgHom.id_apply]
  rw [show of B f i b ⊗ₜ[A] m = (of B f i b ⊗ₜ[A] 1) * (1 ⊗ₜ m) by
    rw [tmul_mul_tmul, mul_one, one_mul], map_mul]
  simp only [toDirectLimit, lift_tmul, map_one, mul_one, one_mul, DirectLimit.Algebra.lift_of,
    AlgHom.comp_apply, includeLeft_apply, includeRight_apply, h1]
  rw [← map_mul, tmul_mul_tmul, mul_one, one_mul]

variable (f) in
/-- Base change commutes with directed colimits of algebras:
`(colim B i) ⊗[A] M ≃ₐ[A] colim (B i ⊗[A] M)`. -/
noncomputable def directLimitLeft :
    DirectLimit B f ⊗[A] M ≃ₐ[A] DirectLimit (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) :=
  AlgEquiv.ofAlgHom (toDirectLimit (f := f) M) (fromDirectLimit M)
    (DirectLimit.Algebra.hom_ext _ fun i ↦ ext' fun b m ↦ by
      rw [AlgHom.comp_apply, AlgHom.comp_apply, AlgHom.comp_apply, fromDirectLimit_of, map_tmul,
        AlgHom.id_apply, toDirectLimit_of_tmul, AlgHom.id_apply])
    (ext' fun b m ↦ by
      obtain ⟨i, b, rfl⟩ := DirectLimit.exists_eq_mk _ b
      rw [← DirectLimit.Algebra.of_apply (R := A), AlgHom.comp_apply, toDirectLimit_of_tmul,
        fromDirectLimit_of, map_tmul, AlgHom.id_apply, AlgHom.id_apply])

theorem directLimitLeft_of_tmul (i : ι) (b : B i) (m : M) :
    directLimitLeft f M (of B f i b ⊗ₜ m) =
      of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) i (b ⊗ₜ m) :=
  toDirectLimit_of_tmul M i b m

theorem directLimitLeft_symm_of (i : ι) (x : B i ⊗[A] M) :
    (directLimitLeft f M).symm (of (B · ⊗[A] M) (fun i j h ↦ rTensor M (f i j h)) i x) =
      rTensor M (of B f i) x := by
  rw [directLimitLeft, AlgEquiv.ofAlgHom_symm]
  exact fromDirectLimit_of (f := f) M i x

end Algebra.TensorProduct

namespace DirectLimit.Algebra

variable [IsDirectedOrder ι] [Nonempty ι]

open Algebra.TensorProduct

/-- Two `A`-algebra maps from an `A`-algebra `S` of finite type into a base change `B j ⊗[A] M`
which agree in `(colim B i) ⊗[A] M` already agree in `B k ⊗[A] M` for some `k ≥ j`. -/
theorem exists_rTensor_comp_eq_rTensor_comp_of_finiteType [Algebra.FiniteType A S] {j : ι}
    {ψ₁ ψ₂ : S →ₐ[A] B j ⊗[A] M}
    (h : (rTensor M (of B f j)).comp ψ₁ = (rTensor M (of B f j)).comp ψ₂) :
    ∃ k, ∃ hjk : j ≤ k, (rTensor M (f j k hjk)).comp ψ₁ = (rTensor M (f j k hjk)).comp ψ₂ :=
  exists_comp_eq_comp_of_finiteType <| AlgHom.ext fun s ↦
    (directLimitLeft f M).symm.injective <| by
    simpa only [AlgHom.comp_apply, directLimitLeft_symm_of] using congr($h s)

/-- **Eventual equality of maps between base changes.** If two `B j`-algebra maps
`Ψ₁ Ψ₂ : B j ⊗[A] S → B j ⊗[A] M`, for `S` of finite type over `A`, have the same base change to
`R = colim B i`, then they have the same base change to `B k` for some `k ≥ j`. -/
theorem exists_rTensor_comp_restrictScalars_eq_of_finiteType [Algebra.FiniteType A S] {j : ι}
    {Ψ₁ Ψ₂ : B j ⊗[A] S →ₐ[B j] B j ⊗[A] M}
    (h : (rTensor M (of B f j)).comp (Ψ₁.restrictScalars A) =
      (rTensor M (of B f j)).comp (Ψ₂.restrictScalars A)) :
    ∃ k, ∃ hjk : j ≤ k, (rTensor M (f j k hjk)).comp (Ψ₁.restrictScalars A) =
      (rTensor M (f j k hjk)).comp (Ψ₂.restrictScalars A) := by
  -- Compare the restrictions along `S → B j ⊗[A] S`; `AlgHom.comp` is definitionally
  -- associative and `restrictScalars A` of an `A`-algebra map is that map, so `hk` is the second
  -- hypothesis of `Algebra.TensorProduct.ext`.
  obtain ⟨k, hjk, hk⟩ := exists_rTensor_comp_eq_rTensor_comp_of_finiteType M
    (ψ₁ := (Ψ₁.restrictScalars A).comp includeRight)
    (ψ₂ := (Ψ₂.restrictScalars A).comp includeRight) congr(AlgHom.comp $h includeRight)
  refine ⟨k, hjk, Algebra.TensorProduct.ext (AlgHom.ext fun b ↦ ?_) hk⟩
  have h₁ := Ψ₁.commutes b
  have h₂ := Ψ₂.commutes b
  simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
    RingHom.id_apply] at h₁ h₂
  simp only [AlgHom.comp_apply, includeLeft_apply, AlgHom.coe_restrictScalars', h₁, h₂]

end DirectLimit.Algebra

end CommSemiring

section CommRing

variable {A ι : Type*} [CommRing A] [Preorder ι] {B : ι → Type*} [∀ i, CommSemiring (B i)]
  [∀ i, Algebra A (B i)] {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]
  {S : Type*} [Semiring S] [Algebra A S] (M : Type*) [CommSemiring M] [Algebra A M]

namespace DirectLimit.Algebra

variable [IsDirectedOrder ι] [Nonempty ι]

open Algebra.TensorProduct

/-- An `A`-algebra map from a finitely presented `A`-algebra into a directed colimit of
`A`-algebras factors through some stage. -/
theorem exists_eq_comp_of_finitePresentation [Algebra.FinitePresentation A S]
    (φ : S →ₐ[A] DirectLimit B f) : ∃ i, ∃ ψ : S →ₐ[A] B i, φ = (of B f i).comp ψ := by
  classical
  obtain ⟨n, π, hπ, s, hs⟩ := Algebra.FinitePresentation.out (R := A) (A := S)
  replace hs : Ideal.span (s : Set _) = RingHom.ker π := hs
  -- Lift the images of the generators to a common stage `i`.
  choose j x hx using fun k : Fin n ↦ DirectLimit.exists_eq_mk _ (φ (π (MvPolynomial.X k)))
  obtain ⟨i, hi⟩ := Finset.exists_le (Finset.univ.image j)
  have hji (k : Fin n) : j k ≤ i := hi _ (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  let ψ₀ : MvPolynomial (Fin n) A →ₐ[A] B i := MvPolynomial.aeval fun k ↦ f (j k) i (hji k) (x k)
  have hψ₀ : (of B f i).comp ψ₀ = φ.comp π := MvPolynomial.algHom_ext fun k ↦ by
    simp [ψ₀, hx]
  -- Each of the finitely many relations dies at some later stage.
  have hrel (r : s) : ∃ m, ∃ him : i ≤ m, f i m him (ψ₀ r) = 0 := by
    have hr : π r = 0 := RingHom.mem_ker.mp (hs ▸ Ideal.subset_span r.2)
    obtain ⟨m, him, hm⟩ := (DirectLimit.exists_eq_zero (f := (f · · ·)) ⟨i, ψ₀ r⟩).mp <| by
      simpa [hr] using congr($hψ₀ r)
    exact ⟨m, him, hm⟩
  choose m him hm using hrel
  obtain ⟨l, hl⟩ := Finset.exists_le (insert i (Finset.univ.image m))
  have hil : i ≤ l := hl i (Finset.mem_insert_self _ _)
  have hml (r : s) : m r ≤ l :=
    hl _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  have hker : RingHom.ker π ≤ RingHom.ker ((f i l hil).comp ψ₀) := by
    rw [← hs, Ideal.span_le]
    intro r hr
    simp [← DirectedSystem.map_map' f (him ⟨r, hr⟩) (hml ⟨r, hr⟩), hm]
  -- The map `MvPolynomial (Fin n) A → B l` descends to `S ≃ MvPolynomial (Fin n) A ⧸ ker π`.
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  have he : e.symm.toAlgHom.comp π = Ideal.Quotient.mkₐ A (RingHom.ker π) :=
    AlgHom.ext fun _ ↦ e.symm_apply_eq.mpr rfl
  refine ⟨l, (Ideal.Quotient.liftₐ _ _ fun a ha ↦ hker ha).comp e.symm.toAlgHom,
    (AlgHom.cancel_right hπ).mp ?_⟩
  rw [← hψ₀, AlgHom.comp_assoc, AlgHom.comp_assoc, he]
  refine AlgHom.ext fun p ↦ ?_
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  -- `Ideal.Quotient.liftₐ` evaluates on `mk p` by definition (`Ideal.Quotient.lift_mk`).
  exact (of_f _ _).symm

/-- An `A`-algebra map from a finitely presented `A`-algebra `S` into the base change
`(colim B i) ⊗[A] M` factors through some `B i ⊗[A] M`. -/
theorem exists_eq_rTensor_comp_of_finitePresentation [Algebra.FinitePresentation A S]
    (φ : S →ₐ[A] DirectLimit B f ⊗[A] M) :
    ∃ i, ∃ ψ : S →ₐ[A] B i ⊗[A] M, φ = (rTensor M (of B f i)).comp ψ := by
  obtain ⟨i, ψ, hψ⟩ :=
    exists_eq_comp_of_finitePresentation ((directLimitLeft f M).toAlgHom.comp φ)
  refine ⟨i, ψ, AlgHom.ext fun s ↦ ?_⟩
  rw [AlgHom.comp_apply, ← directLimitLeft_symm_of, ← AlgHom.comp_apply, ← hψ]
  exact ((directLimitLeft f M).symm_apply_apply (φ s)).symm

/-- **Descent of maps between base changes.** Let `R = colim B i`. Every `R`-algebra map
`Φ : R ⊗[A] S → R ⊗[A] M`, for `S` finitely presented over `A`, is the base change of a
`B i`-algebra map `Ψ : B i ⊗[A] S → B i ⊗[A] M` for some `i`: the two agree on the image of
`B i ⊗[A] S`, which generates `R ⊗[A] S` as an `R`-algebra. -/
theorem exists_restrictScalars_comp_rTensor_eq_of_finitePresentation
    [Algebra.FinitePresentation A S]
    (Φ : DirectLimit B f ⊗[A] S →ₐ[DirectLimit B f] DirectLimit B f ⊗[A] M) :
    ∃ i, ∃ Ψ : B i ⊗[A] S →ₐ[B i] B i ⊗[A] M,
      (Φ.restrictScalars A).comp (rTensor S (of B f i)) =
        (rTensor M (of B f i)).comp (Ψ.restrictScalars A) := by
  obtain ⟨i, ψ, hψ⟩ :=
    exists_eq_rTensor_comp_of_finitePresentation M ((Φ.restrictScalars A).comp includeRight)
  refine ⟨i, AlgHom.liftEquiv A (B i) S _ ψ,
    Algebra.TensorProduct.ext (AlgHom.ext fun b ↦ ?_) (AlgHom.ext fun s ↦ ?_)⟩
  · have h₁ := Φ.commutes (of B f i b)
    have h₂ := (AlgHom.liftEquiv A (B i) S _ ψ).commutes b
    simp only [Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self,
      RingHom.id_apply] at h₁ h₂
    simp only [AlgHom.comp_apply, includeLeft_apply, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgHom.coe_restrictScalars', h₁, h₂]
  · simpa [-DirectLimit.Algebra.of_apply] using congr($hψ s)

end DirectLimit.Algebra

end CommRing
