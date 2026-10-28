/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.FinitePresentation
public import TauCeti.RingTheory.TensorProduct.DirectLimit
import Mathlib.Data.Fintype.Order

/-!
# Algebra maps from finitely presented algebras into directed colimits

Let `B i` be a directed system of `A`-algebras, indexed by a nonempty directed preorder, with
`A`-algebra transition maps `f i j`, and let `DirectLimit B f` be its colimit, an `A`-algebra.
This file shows that `Hom_A(S, -)` commutes with this colimit when `S` is finitely presented:

* an `A`-algebra map from a finitely presented `S` into the colimit factors through some stage;
* two `A`-algebra maps from an `A`-algebra `S` of finite type into a stage that agree in the
  colimit already agree at a later stage.

Combining these with the equivalence `(colim B i) ⊗[A] M ≃ₐ[A] colim (B i ⊗[A] M)` of
`TauCeti.directLimitLeft`, maps from a finitely presented
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

* `TauCeti.DirectLimit.Algebra.exists_eq_comp_of_finitePresentation`: an `A`-algebra map from a
  finitely presented `A`-algebra into a directed colimit of `A`-algebras factors through some
  stage.
* `TauCeti.DirectLimit.Algebra.exists_comp_eq_comp_of_finiteType`: two `A`-algebra maps from an
  `A`-algebra of finite type into a stage which agree in the colimit agree at a later stage.
* `TauCeti.DirectLimit.Algebra.exists_eq_rTensor_comp_of_finitePresentation`,
  `TauCeti.DirectLimit.Algebra.exists_rTensor_comp_eq_rTensor_comp_of_finiteType`: the same two
  statements for maps `S → (colim B i) ⊗[A] M`.
* `TauCeti.DirectLimit.Algebra.exists_restrictScalars_comp_rTensor_eq_of_finitePresentation`,
  `TauCeti.DirectLimit.Algebra.exists_rTensor_comp_restrictScalars_eq_of_finiteType`: descent
  and eventual equality of maps between base changes `R ⊗[A] S → R ⊗[A] M`, for `S` finitely
  presented.

## References

* K. S. Kedlaya and R. Liu, *Relative p-adic Hodge theory: foundations*, Astérisque 371 (2015),
  Remark 1.2.9.
-/

public section

open scoped TensorProduct

namespace TauCeti

namespace DirectLimit.Algebra

open _root_.DirectLimit.Algebra

section Semiring

variable {A ι : Type*} [CommSemiring A] [Preorder ι] {B : ι → Type*} [∀ i, Semiring (B i)]
  [∀ i, Algebra A (B i)] {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]
  [IsDirectedOrder ι] [Nonempty ι] {S : Type*} [Semiring S] [Algebra A S]

/-- Two `A`-algebra maps from an `A`-algebra of finite type into a stage of a directed colimit of
`A`-algebras which agree in the colimit already agree at a later stage. -/
theorem exists_comp_eq_comp_of_finiteType [Algebra.FiniteType A S] {j : ι}
    {ψ₁ ψ₂ : S →ₐ[A] B j} (h : (of B f j).comp ψ₁ = (of B f j).comp ψ₂) :
    ∃ k, ∃ hjk : j ≤ k, (f j k hjk).comp ψ₁ = (f j k hjk).comp ψ₂ := by
  classical
  obtain ⟨s, hs⟩ := (Algebra.FiniteType.out : (⊤ : Subalgebra A S).FG)
  -- Each of the finitely many generators is equalized at some later stage.
  have hgen (x : s) : ∃ k, ∃ hjk : j ≤ k, f j k hjk (ψ₁ x) = f j k hjk (ψ₂ x) := by
    have hx := congr($h x)
    simp only [AlgHom.comp_apply, DirectLimit.Algebra.of_apply] at hx
    obtain ⟨k, hk₁, hk₂, hk⟩ := Quotient.eq.mp hx
    exact ⟨k, hk₁, hk⟩
  choose k hjk hk using hgen
  obtain ⟨l₀, hl₀⟩ := Finite.exists_le k
  obtain ⟨l, hjl, hl₀l⟩ := exists_ge_ge j l₀
  have hkl (x : s) : k x ≤ l := (hl₀ x).trans hl₀l
  refine ⟨l, hjl, AlgHom.ext_of_adjoin_eq_top hs fun x hx ↦ ?_⟩
  simp only [AlgHom.comp_apply]
  rw [← DirectedSystem.map_map' f (hjk ⟨x, hx⟩) (hkl ⟨x, hx⟩), hk]
  exact DirectedSystem.map_map' f _ _ _

variable (M : Type*) [Semiring M] [Algebra A M]

open _root_.Algebra.TensorProduct

/-- Two `A`-algebra maps from an `A`-algebra `S` of finite type into a base change `B j ⊗[A] M`
which agree in `(colim B i) ⊗[A] M` already agree in `B k ⊗[A] M` for some `k ≥ j`. -/
theorem exists_rTensor_comp_eq_rTensor_comp_of_finiteType [Algebra.FiniteType A S] {j : ι}
    {ψ₁ ψ₂ : S →ₐ[A] B j ⊗[A] M}
    (h : (rTensor M (of B f j)).comp ψ₁ = (rTensor M (of B f j)).comp ψ₂) :
    ∃ k, ∃ hjk : j ≤ k, (rTensor M (f j k hjk)).comp ψ₁ = (rTensor M (f j k hjk)).comp ψ₂ :=
  exists_comp_eq_comp_of_finiteType <| by
    simpa only [← AlgHom.comp_assoc, directLimitLeft_comp_rTensor_of] using
      congr((directLimitLeft f M).toAlgHom.comp $h)

end Semiring

section CommSemiring

variable {A ι : Type*} [CommSemiring A] [Preorder ι] {B : ι → Type*} [∀ i, CommSemiring (B i)]
  [∀ i, Algebra A (B i)] {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]
  [IsDirectedOrder ι] [Nonempty ι] {S : Type*} [Semiring S] [Algebra A S]
  (M : Type*) [Semiring M] [Algebra A M]

open _root_.Algebra.TensorProduct

/-- A map of `R`-algebras `R ⊗[A] S → R ⊗[A] M` fixes `r ⊗ₜ 1`, the image of `r` under the
algebra map. -/
private theorem map_tmul_one {R : Type*} [CommSemiring R] [Algebra A R]
    (Ψ : R ⊗[A] S →ₐ[R] R ⊗[A] M) (r : R) : Ψ (r ⊗ₜ 1) = r ⊗ₜ 1 := by
  simpa using Ψ.commutes r

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
  simp only [AlgHom.comp_apply, includeLeft_apply, AlgHom.coe_restrictScalars', map_tmul_one]

end CommSemiring

section CommRing

variable {A ι : Type*} [CommRing A] [Preorder ι] {B : ι → Type*} [∀ i, CommSemiring (B i)]
  [∀ i, Algebra A (B i)] {f : ∀ i j, i ≤ j → B i →ₐ[A] B j} [DirectedSystem B (f · · ·)]
  [IsDirectedOrder ι] [Nonempty ι] {S : Type*} [Semiring S] [Algebra A S]
  (M : Type*) [CommSemiring M] [Algebra A M]

open _root_.Algebra.TensorProduct

/-- An `A`-algebra map from a finitely presented `A`-algebra into a directed colimit of
`A`-algebras factors through some stage. -/
theorem exists_eq_comp_of_finitePresentation [Algebra.FinitePresentation A S]
    (φ : S →ₐ[A] DirectLimit B f) : ∃ i, ∃ ψ : S →ₐ[A] B i, φ = (of B f i).comp ψ := by
  classical
  obtain ⟨n, π, hπ, s, hs⟩ := Algebra.FinitePresentation.out (R := A) (A := S)
  rw [AlgHom.toRingHom_eq_coe, RingHom.ker_coe_toRingHom] at hs
  -- Lift the images of the generators to a common stage `i`.
  choose j x hx using fun k : Fin n ↦ DirectLimit.exists_eq_mk _ (φ (π (MvPolynomial.X k)))
  obtain ⟨i, hji⟩ := Finite.exists_le j
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
  obtain ⟨l₀, hl₀⟩ := Finite.exists_le m
  obtain ⟨l, hil, hl₀l⟩ := exists_ge_ge i l₀
  have hml (r : s) : m r ≤ l := (hl₀ r).trans hl₀l
  have hker : RingHom.ker π ≤ RingHom.ker ((f i l hil).comp ψ₀) := by
    rw [← hs, Ideal.span_le]
    intro r hr
    simp [← DirectedSystem.map_map' f (him ⟨r, hr⟩) (hml ⟨r, hr⟩), hm]
  -- The map `MvPolynomial (Fin n) A → B l` descends to `S ≃ MvPolynomial (Fin n) A ⧸ ker π`.
  let e := Ideal.quotientKerAlgEquivOfSurjective hπ
  have he : e.symm.toAlgHom.comp π = Ideal.Quotient.mkₐ A (RingHom.ker π) :=
    AlgHom.ext fun _ ↦ Ideal.quotientKerAlgEquivOfSurjective_symm_apply hπ _
  refine ⟨l, (Ideal.Quotient.liftₐ _ _ fun a ha ↦ RingHom.mem_ker.mp (hker ha)).comp
    e.symm.toAlgHom, (AlgHom.cancel_right hπ).mp ?_⟩
  -- Both sides become `(of B f l).comp ((f i l hil).comp ψ₀)`.
  simp only [← hψ₀, ← of_comp_f hil, AlgHom.comp_assoc, he, Ideal.Quotient.liftₐ_comp]

/-- An `A`-algebra map from a finitely presented `A`-algebra `S` into the base change
`(colim B i) ⊗[A] M` factors through some `B i ⊗[A] M`. -/
theorem exists_eq_rTensor_comp_of_finitePresentation [Algebra.FinitePresentation A S]
    (φ : S →ₐ[A] DirectLimit B f ⊗[A] M) :
    ∃ i, ∃ ψ : S →ₐ[A] B i ⊗[A] M, φ = (rTensor M (of B f i)).comp ψ := by
  obtain ⟨i, ψ, hψ⟩ :=
    exists_eq_comp_of_finitePresentation ((directLimitLeft f M).toAlgHom.comp φ)
  refine ⟨i, ψ, ?_⟩
  rw [← directLimitLeft_symm_comp_of, AlgHom.comp_assoc, ← hψ, ← AlgHom.comp_assoc,
    AlgEquiv.symm_comp, AlgHom.id_comp]

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
  · simp only [AlgHom.comp_apply, includeLeft_apply, Algebra.TensorProduct.map_tmul,
      AlgHom.id_apply, AlgHom.coe_restrictScalars', map_tmul_one]
  · simpa [-DirectLimit.Algebra.of_apply] using congr($hψ s)

end CommRing

end DirectLimit.Algebra

end TauCeti
