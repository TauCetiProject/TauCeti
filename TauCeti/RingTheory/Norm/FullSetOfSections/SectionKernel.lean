/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Norm.FullSetOfSections.Basic
import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.Matrix.Block
import TauCeti.RingTheory.Norm.Quotient

/-!
# Norms at algebra retractions and full sets of sections along principal kernels

This file proves two ring-theoretic mechanisms that relate norms and full sets of sections to
algebra retractions and principal ideals:

1. **Cayley–Hamilton vanishing at a retraction**: if `B` is a finite free `A`-algebra and an
   `A`-algebra map `τ : B →ₐ[A] A` kills `b : B`, then `Algebra.norm A b = 0`
   (`TauCeti.Algebra.norm_eq_zero_of_algHom_eq_zero`). More generally, if `τ : B →ₐ[A] A ⧸ I` kills
   `b`, then `Algebra.norm A b ∈ I` (`TauCeti.Algebra.norm_mem_ideal_of_algHom_quotient`).
   Evaluating the characteristic polynomial `p(X)` of multiplication by `b` at `b` gives `0` in `B`
   by Cayley–Hamilton; applying `τ` yields `p(0) = 0`, and the constant term of `p` is, up to sign,
   `Algebra.norm A b`.

2. **Inductive extension of a full set of sections by a principal section kernel**: suppose `B'` is
   a finite free `A`-algebra, `σ : B →ₐ[A] A` is a retraction, `π : B →ₐ[A] B'` is a surjective
   `A`-algebra homomorphism, and an element `u : B` satisfies `ker σ = (u)` and `ker π = Ann(u)`.
   Multiplication by `u` identifies `B' ≃ B ⧸ Ann(u)` `B`-linearly with `ker σ`, while `σ` splits
   the `A`-linear sequence `0 → B' → B → A → 0`. After any base change `A → T`, multiplication by
   `f ∈ T ⊗[A] B` is block upper-triangular on `(T ⊗[A] B') × T`, with diagonal blocks
   multiplication by `(1 ⊗ π)(f)` and multiplication by `σ_T(f)`. Taking determinants gives
   `Algebra.norm T f = σ_T(f) * Algebra.norm T ((1 ⊗ π)(f))`
   (`TauCeti.Algebra.norm_eq_mul_of_ker_span_singleton`), so adjoining `σ` to the pullback along `π`
   of a full set of sections of `B'` produces a full set of sections of `B`
   (`TauCeti.IsFullSetOfSections.optionElim_of_ker_span_singleton`).

Geometrically, for an effective Cartier divisor `I₁ = [x_a]` given by a section and a finite flat
divisor `D'` on a smooth curve over a local base `Spec A`, the closed subscheme `V(I₁ * D')` has
coordinate ring `B` with `ker σ = (u)` and `ker π = Ann(u)`, giving the inductive step from `D'` to
`I₁ * D'`.

## Main results

* `TauCeti.Algebra.norm_eq_zero_of_algHom_eq_zero`: an `A`-algebra retraction killing `b` forces
  `Algebra.norm A b = 0`.
* `TauCeti.Algebra.norm_mem_ideal_of_algHom_quotient`: an `A`-algebra map `B →ₐ[A] A ⧸ I` killing
  `b` forces `Algebra.norm A b ∈ I`.
* `TauCeti.isFullSetOfSections_of_subsingleton` and `TauCeti.isFullSetOfSections_comp_equiv_iff`:
  full sets of sections of a subsingleton algebra and reindexing of full sets of sections.
* `TauCeti.Algebra.norm_eq_mul_of_ker_span_singleton` and
  `TauCeti.IsFullSetOfSections.optionElim_of_ker_span_singleton`: multiplicativity of the norm and
  extension of a full set of sections across `ker σ = (u)`, `ker π = Ann(u)`.

## References

* N. M. Katz and B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, Theorem 1.8.3.
-/

public section

open TensorProduct Polynomial

namespace TauCeti

/-! ### Vanishing of the norm at an algebra retraction -/

/-- **Cayley–Hamilton vanishing of the norm at a retraction.** Over a commutative ring `A`, if `B`
is a finite free `A`-algebra and an `A`-algebra homomorphism `τ : B →ₐ[A] A` vanishes at `b : B`,
then `Algebra.norm A b = 0`. -/
theorem Algebra.norm_eq_zero_of_algHom_eq_zero {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Free A B] [Module.Finite A B] (τ : B →ₐ[A] A) {b : B}
    (hb : τ b = 0) : Algebra.norm A b = 0 := by
  let p := (Algebra.lmul A B b).charpoly
  have h0 : p.coeff 0 = 0 := by
    have hτ := congrArg τ (_root_.Algebra.aeval_self_charpoly_lmul (R := A) b)
    rwa [map_zero, ← aeval_algHom_apply, hb, aeval_def, eval₂_at_zero, Algebra.algebraMap_self,
      RingHom.id_apply] at hτ
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, h0, mul_zero]

/-- **Congruence vanishing of the norm at a quotient retraction.** If `B` is a finite free
`A`-algebra, `I` is an ideal of `A`, and `τ : B →ₐ[A] A ⧸ I` vanishes at `b : B`, then
`Algebra.norm A b ∈ I`. -/
theorem Algebra.norm_mem_ideal_of_algHom_quotient {A B : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Free A B] [Module.Finite A B] {I : Ideal A} (τ : B →ₐ[A] A ⧸ I)
    {b : B} (hb : τ b = 0) : Algebra.norm A b ∈ I := by
  let τ' : (A ⧸ I) ⊗[A] B →ₐ[A ⧸ I] A ⧸ I :=
    Algebra.TensorProduct.lift (Algebra.ofId (A ⧸ I) (A ⧸ I)) τ fun _ _ ↦ Commute.all _ _
  have h0 : Algebra.norm (A ⧸ I) ((1 : A ⧸ I) ⊗ₜ[A] b) = 0 :=
    Algebra.norm_eq_zero_of_algHom_eq_zero τ' (by simp [τ', hb])
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← Algebra.norm_quotient_mk I b,
    ← Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I),
    Algebra.TensorProduct.quotIdealMapEquivQuotTensor_mk]
  exact h0

/-! ### Subsingleton and reindexed full sets of sections -/

/-- Any finite family of sections of a subsingleton algebra is a full set of sections. -/
theorem isFullSetOfSections_of_subsingleton {A B ι : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Subsingleton B] [Fintype ι] (s : ι → B →ₐ[A] A) :
    IsFullSetOfSections s := by
  rw [isFullSetOfSections_iff]
  intro T _ _ _ f
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨i₀⟩⟩
  · have : Subsingleton (T ⊗[A] B) := inferInstance
    rw [Subsingleton.elim f 1, map_one, Finset.univ_eq_empty, Finset.prod_empty]
  · have : Subsingleton A := subsingleton_of_zero_eq_one <| by
      rw [← map_zero (s i₀), ← map_one (s i₀), Subsingleton.elim (0 : B) 1]
    have : Subsingleton T := subsingleton_of_zero_eq_one <| by
      rw [← map_zero (algebraMap A T), ← map_one (algebraMap A T), Subsingleton.elim (0 : A) 1]
    exact Subsingleton.elim _ _

/-- Being a full set of sections is invariant under reindexing by an equivalence. -/
theorem isFullSetOfSections_comp_equiv_iff {A B ι ι' : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [Fintype ι] [Fintype ι'] {s : ι → B →ₐ[A] A} (e : ι' ≃ ι) :
    IsFullSetOfSections (s ∘ e) ↔ IsFullSetOfSections s := by
  rw [isFullSetOfSections_iff, isFullSetOfSections_iff]
  refine forall_congr' fun T ↦ forall_congr' fun _ ↦ forall_congr' fun _ ↦
    forall_congr' fun _ ↦ forall_congr' fun f ↦ ?_
  simp only [Function.comp_apply]
  rw [Fintype.prod_equiv e (fun j ↦ (s (e j)).sectionBaseChange T f)
    (fun i ↦ (s i).sectionBaseChange T f) fun _ ↦ rfl]

/-! ### Principal section kernels and block-triangular norms -/

section PrincipalKernel

variable {A B B' : Type*} [CommRing A] [CommRing B] [Algebra A B] [CommRing B'] [Algebra A B']

/-- When `ker π = Ann(u)`, multiplication by `u` descends from `B ⧸ ker π` to an `A`-linear
isomorphism `(B ⧸ ker π) ≃ₗ[A] (u)`. -/
private noncomputable def mulSpanQuotEquiv {π : B →ₐ[A] B'} {u : B}
    (hkerπ : RingHom.ker π = (Ideal.span {u}).annihilator) :
    (B ⧸ RingHom.ker π) ≃ₗ[A] (Ideal.span ({u} : Set B)).restrictScalars A := by
  let μ : B →ₗ[A] (Ideal.span ({u} : Set B)).restrictScalars A :=
    (LinearMap.mulRight A u).codRestrict ((Ideal.span {u}).restrictScalars A) fun b ↦
      Ideal.mem_span_singleton.mpr ⟨b, mul_comm b u⟩
  have hμ (b : B) : (μ b : B) = b * u := rfl
  have hkerμ : LinearMap.ker μ = (RingHom.ker π).restrictScalars A := by
    ext b
    simp [LinearMap.mem_ker, Subtype.ext_iff, hμ, hkerπ, Ideal.span, mul_comm]
  have hsurjμ : Function.Surjective μ := by
    rintro ⟨x, hx⟩
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hx
    exact ⟨b, Subtype.ext (mul_comm b u)⟩
  exact (Submodule.Quotient.restrictScalarsEquiv A (RingHom.ker π)).symm ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hkerμ.symm ≪≫ₗ
    LinearMap.quotKerEquivOfSurjective μ hsurjμ

/-- When `π : B →ₐ[A] B'` is surjective with `ker π = Ann(u)`, multiplication by `u` descends to an
`A`-linear isomorphism `B' ≃ₗ[A] (u)`. -/
private noncomputable def mulSpanEquiv {π : B →ₐ[A] B'} (hπ : Function.Surjective π) {u : B}
    (hkerπ : RingHom.ker π = (Ideal.span {u}).annihilator) :
    B' ≃ₗ[A] (Ideal.span ({u} : Set B)).restrictScalars A :=
  (Ideal.quotientKerAlgEquivOfSurjective hπ).symm.toLinearEquiv ≪≫ₗ mulSpanQuotEquiv hkerπ

private lemma coe_mulSpanEquiv_apply_pi {π : B →ₐ[A] B'} (hπ : Function.Surjective π) {u : B}
    (hkerπ : RingHom.ker π = (Ideal.span {u}).annihilator) (b : B) :
    (mulSpanEquiv hπ hkerπ (π b) : B) = b * u :=
  congrArg (fun q ↦ (mulSpanQuotEquiv hkerπ q : B))
    ((Ideal.quotientKerAlgEquivOfSurjective hπ).symm_apply_apply
      (Ideal.Quotient.mk (RingHom.ker π) b))

private lemma mul_coe_mulSpanEquiv {π : B →ₐ[A] B'} (hπ : Function.Surjective π) {u : B}
    (hkerπ : RingHom.ker π = (Ideal.span {u}).annihilator) (b : B) (y : B') :
    b * (mulSpanEquiv hπ hkerπ y : B) = (mulSpanEquiv hπ hkerπ (π b * y) : B) := by
  obtain ⟨c, rfl⟩ := hπ y
  rw [← map_mul, coe_mulSpanEquiv_apply_pi, coe_mulSpanEquiv_apply_pi, mul_assoc]

/-- The `A`-linear retraction `B →ₗ[A] B'` dual to `mulSpanEquiv` along `σ : B →ₐ[A] A`. -/
private noncomputable def kerSpanRetr {σ : B →ₐ[A] A} {π : B →ₐ[A] B'}
    (hπ : Function.Surjective π) {u : B} (hσ : RingHom.ker σ = Ideal.span {u})
    (hkerπ : RingHom.ker π = (Ideal.span {u}).annihilator) : B →ₗ[A] B' :=
  let eK : B' ≃ₗ[A] (RingHom.ker σ).restrictScalars A :=
    mulSpanEquiv hπ hkerπ ≪≫ₗ LinearEquiv.ofEq _ _ (congrArg (Submodule.restrictScalars A) hσ.symm)
  let pK : B →ₗ[A] (RingHom.ker σ).restrictScalars A :=
    { toFun := fun b ↦ ⟨b - algebraMap A B (σ b), by simp [RingHom.mem_ker]⟩
      map_add' := fun x y ↦ Subtype.ext (by simp [sub_add_sub_comm])
      map_smul' := fun r x ↦ Subtype.ext (by simp [Algebra.smul_def, mul_sub]) }
  eK.symm.toLinearMap.comp pK

private lemma kerSpanRetr_properties {σ : B →ₐ[A] A} {π : B →ₐ[A] B'}
    (hπ : Function.Surjective π) {u : B} (hσ : RingHom.ker σ = Ideal.span {u})
    (hkerπ : RingHom.ker π = (Ideal.span {u}).annihilator) :
    let φ : B' →ₗ[A] B := ((Ideal.span ({u} : Set B)).restrictScalars A).subtype.comp
      (mulSpanEquiv hπ hkerπ).toLinearMap
    let ρ := kerSpanRetr hπ hσ hkerπ
    ρ 1 = 0 ∧ (∀ y, ρ (φ y) = y) ∧ (∀ y, σ (φ y) = 0) ∧
      ∀ b, φ (ρ b) + algebraMap A B (σ b) = b := by
  intro φ ρ
  let eK : B' ≃ₗ[A] (RingHom.ker σ).restrictScalars A :=
    mulSpanEquiv hπ hkerπ ≪≫ₗ LinearEquiv.ofEq _ _ (congrArg (Submodule.restrictScalars A) hσ.symm)
  have hφeK (y : B') : φ y = (eK y : B) := rfl
  have hσy (y : B') : σ (φ y) = 0 := RingHom.mem_ker.mp (eK y).2
  refine ⟨?_, fun y ↦ ?_, hσy, fun b ↦ ?_⟩
  · simp [ρ, kerSpanRetr]
  · have hsub : (⟨φ y - algebraMap A B (σ (φ y)), by simp [RingHom.mem_ker]⟩ :
        (RingHom.ker σ).restrictScalars A) = eK y := by
      apply Subtype.ext
      dsimp only
      rw [hσy y, map_zero, sub_zero, hφeK]
    exact (congrArg eK.symm hsub).trans (eK.symm_apply_apply y)
  · have hval : (eK (ρ b) : B) = b - algebraMap A B (σ b) :=
      congrArg Subtype.val
        (eK.apply_symm_apply ⟨b - algebraMap A B (σ b), by simp [RingHom.mem_ker]⟩)
    rw [hφeK, hval, sub_add_cancel]

/-- The `T`-linear splitting `(T ⊗[A] B') × T ≃ₗ[T] T ⊗[A] B` induced by `σ : B →ₐ[A] A` and
`ker σ = (u)`, `ker π = Ann(u)`. -/
private noncomputable def splitBaseChangeEquiv {σ : B →ₐ[A] A} {π : B →ₐ[A] B'}
    (hπ : Function.Surjective π) {u : B} (hσ : RingHom.ker σ = Ideal.span {u})
    (hkerπ : RingHom.ker π = (Ideal.span {u}).annihilator) (T : Type*) [CommRing T]
    [Algebra A T] : ((T ⊗[A] B') × T) ≃ₗ[T] T ⊗[A] B := by
  let φ : B' →ₗ[A] B := ((Ideal.span ({u} : Set B)).restrictScalars A).subtype.comp
    (mulSpanEquiv hπ hkerπ).toLinearMap
  let ρ := kerSpanRetr hπ hσ hkerπ
  have hρ1 : ρ 1 = 0 := (kerSpanRetr_properties hπ hσ hkerπ).1
  have hρφ (y : B') : ρ (φ y) = y := (kerSpanRetr_properties hπ hσ hkerπ).2.1 y
  have hσy (y : B') : σ (φ y) = 0 := (kerSpanRetr_properties hπ hσ hkerπ).2.2.1 y
  have hφρ (b : B) : φ (ρ b) + algebraMap A B (σ b) = b :=
    (kerSpanRetr_properties hπ hσ hkerπ).2.2.2 b
  have h1 (z : T ⊗[A] B') : ρ.baseChange T (φ.baseChange T z) = z := by
    induction z using TensorProduct.inductionOn with
    | tmul s y => simp [hρφ]
    | add z₁ z₂ hz₁ hz₂ => rw [map_add, map_add, hz₁, hz₂]
  have h3 (z : T ⊗[A] B') : σ.sectionBaseChange T (φ.baseChange T z) = 0 := by
    induction z using TensorProduct.inductionOn with
    | tmul s y => simp [AlgHom.sectionBaseChange_tmul, hσy]
    | add z₁ z₂ hz₁ hz₂ => rw [map_add, map_add, hz₁, hz₂, add_zero]
  have h5 (x : T ⊗[A] B) :
      φ.baseChange T (ρ.baseChange T x) +
        algebraMap T (T ⊗[A] B) (σ.sectionBaseChange T x) = x := by
    induction x using TensorProduct.inductionOn with
    | tmul t b =>
      simp only [LinearMap.baseChange_tmul, AlgHom.sectionBaseChange_tmul,
        Algebra.TensorProduct.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply]
      rw [mul_comm t, ← Algebra.smul_def, TensorProduct.smul_tmul, Algebra.smul_def, mul_one,
        ← TensorProduct.tmul_add, hφρ]
    | add x₁ x₂ hx₁ hx₂ => rw [map_add, map_add, map_add, map_add, add_add_add_comm, hx₁, hx₂]
  refine LinearEquiv.ofLinearMap
    (LinearMap.coprod (φ.baseChange T) (Algebra.linearMap T (T ⊗[A] B)))
    (LinearMap.prod (ρ.baseChange T) (σ.sectionBaseChange T).toLinearMap) ?_ ?_
  · apply LinearMap.ext; intro x
    exact h5 x
  · apply LinearMap.ext; rintro ⟨z, t⟩
    exact Prod.ext (by simp [map_add, h1, hρ1]) (by simp [map_add, h3])

/-- Under `splitBaseChangeEquiv`, multiplication by `f` on `T ⊗[A] B` acts on `(z, 0)` as
`((1 ⊗ π)(f) * z, 0)` and on the second coordinate `(z, t)` as `σ_T(f) * t`. -/
private lemma splitBaseChangeEquiv_conj_apply {σ : B →ₐ[A] A} {π : B →ₐ[A] B'}
    (hπ : Function.Surjective π) {u : B} (hσ : RingHom.ker σ = Ideal.span {u})
    (hkerπ : RingHom.ker π = (Ideal.span {u}).annihilator) {T : Type*} [CommRing T]
    [Algebra A T] (f : T ⊗[A] B) (z : T ⊗[A] B') (t : T) :
    (splitBaseChangeEquiv hπ hσ hkerπ T).symm (f * splitBaseChangeEquiv hπ hσ hkerπ T (z, 0)) =
        (Algebra.TensorProduct.map (AlgHom.id T T) π f * z, 0) ∧
      ((splitBaseChangeEquiv hπ hσ hkerπ T).symm
        (f * splitBaseChangeEquiv hπ hσ hkerπ T (z, t))).2 = σ.sectionBaseChange T f * t := by
  let e := splitBaseChangeEquiv hπ hσ hkerπ T
  let φ : B' →ₗ[A] B := ((Ideal.span ({u} : Set B)).restrictScalars A).subtype.comp
    (mulSpanEquiv hπ hkerπ).toLinearMap
  have he_inl (w : T ⊗[A] B') : e (w, 0) = φ.baseChange T w := by
    simp [e, splitBaseChangeEquiv, φ]
  refine ⟨?_, ?_⟩
  · apply e.injective
    rw [e.apply_symm_apply, he_inl, he_inl]
    induction f using TensorProduct.inductionOn with
    | tmul r b =>
      induction z using TensorProduct.inductionOn with
      | tmul s y =>
        simp only [Algebra.TensorProduct.tmul_mul_tmul, LinearMap.baseChange_tmul,
          Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
        exact congrArg ((r * s) ⊗ₜ[A] ·) (mul_coe_mulSpanEquiv hπ hkerπ b y)
      | add z₁ z₂ h₁ h₂ => simp [mul_add, h₁, h₂]
    | add f₁ f₂ h₁ h₂ => simp [add_mul, h₁, h₂]
  · have hσ_inl (w : T ⊗[A] B') : σ.sectionBaseChange T (e (w, 0)) = 0 := by
      have := congrArg Prod.snd (e.symm_apply_apply (w, 0))
      simpa [e, splitBaseChangeEquiv] using this
    have he_pair : e (z, t) = e (z, 0) + algebraMap T (T ⊗[A] B) t := by
      simp [e, splitBaseChangeEquiv]
    have hfst : (e.symm (f * e (z, t))).2 = σ.sectionBaseChange T (f * e (z, t)) := rfl
    rw [hfst, he_pair, map_mul, map_add, hσ_inl, zero_add, AlgHom.commutes,
      Algebra.algebraMap_self, RingHom.id_apply]

/-- If `B'` is finite free over `A`, `σ : B →ₐ[A] A`, `π : B →ₐ[A] B'` is surjective,
`ker σ = (u)` and `ker π = Ann(u)`, then `B` is finite free over `A`. -/
theorem moduleFree_and_finite_of_ker_span_singleton [Module.Free A B'] [Module.Finite A B']
    {σ : B →ₐ[A] A} {π : B →ₐ[A] B'} (hπ : Function.Surjective π) {u : B}
    (hσ : RingHom.ker σ = Ideal.span {u}) (hkerπ : RingHom.ker π = (Ideal.span {u}).annihilator) :
    Module.Free A B ∧ Module.Finite A B := by
  let e : ((A ⊗[A] B') × A) ≃ₗ[A] B :=
    splitBaseChangeEquiv hπ hσ hkerπ A ≪≫ₗ (Algebra.TensorProduct.lid A B).toLinearEquiv
  exact ⟨.of_equiv e, .equiv e⟩

/-- **Multiplicativity of the norm across a principal section kernel.** Suppose `B'` is finite free
over `A`, `σ : B →ₐ[A] A`, `π : B →ₐ[A] B'` is surjective, `ker σ = (u)` and `ker π = Ann(u)`.
Then for every `A`-algebra `T` and every `f ∈ T ⊗[A] B`, the norm of `f` over `T` is
`σ_T(f) * Algebra.norm T ((1 ⊗ π)(f))`. -/
theorem Algebra.norm_eq_mul_of_ker_span_singleton [Module.Free A B'] [Module.Finite A B']
    {σ : B →ₐ[A] A} {π : B →ₐ[A] B'} (hπ : Function.Surjective π) {u : B}
    (hσ : RingHom.ker σ = Ideal.span {u}) (hkerπ : RingHom.ker π = (Ideal.span {u}).annihilator)
    (T : Type*) [CommRing T] [Algebra A T] (f : T ⊗[A] B) :
    Algebra.norm T f =
      σ.sectionBaseChange T f *
        Algebra.norm T (Algebra.TensorProduct.map (AlgHom.id T T) π f) := by
  classical
  let e := splitBaseChangeEquiv hπ hσ hkerπ T
  let M : ((T ⊗[A] B') × T) →ₗ[T] (T ⊗[A] B') × T :=
    e.symm.toLinearMap ∘ₗ Algebra.lmul T (T ⊗[A] B) f ∘ₗ e.toLinearMap
  have hdet : LinearMap.det (Algebra.lmul T (T ⊗[A] B) f) = LinearMap.det M := by
    simpa [M] using (LinearMap.det_conj (Algebra.lmul T (T ⊗[A] B) f) e.symm).symm
  let m := Module.Free.ChooseBasisIndex T (T ⊗[A] B')
  let b₁ : Module.Basis m T (T ⊗[A] B') := Module.Free.chooseBasis T (T ⊗[A] B')
  let b₂ : Module.Basis Unit T T := Module.Basis.singleton Unit T
  let b := b₁.prod b₂
  let f' := Algebra.TensorProduct.map (AlgHom.id T T) π f
  let A₁₁ : Matrix m m T := LinearMap.toMatrix b₁ b₁ (Algebra.lmul T (T ⊗[A] B') f')
  let A₁₂ : Matrix m Unit T := Matrix.of fun i _ ↦ b₁.repr (M (0, 1)).1 i
  let A₂₂ : Matrix Unit Unit T :=
    LinearMap.toMatrix b₂ b₂ (Algebra.lmul T T (σ.sectionBaseChange T f))
  have hmat : LinearMap.toMatrix b b M = Matrix.fromBlocks A₁₁ A₁₂ 0 A₂₂ := by
    ext (i | _) (j | _)
    · have h1 := (splitBaseChangeEquiv_conj_apply hπ hσ hkerπ f (b₁ j) 0).1
      simp [b, M, e, A₁₁, f', LinearMap.toMatrix_apply, h1]
    · simp [b, b₂, A₁₂, LinearMap.toMatrix_apply]
    · have h1 := (splitBaseChangeEquiv_conj_apply hπ hσ hkerπ f (b₁ j) 0).1
      simp [b, M, e, LinearMap.toMatrix_apply, h1]
    · have h2 := (splitBaseChangeEquiv_conj_apply hπ hσ hkerπ f 0 1).2
      simp [b, b₂, M, e, A₂₂, LinearMap.toMatrix_apply, h2]
  rw [Algebra.norm_apply, hdet, ← LinearMap.det_toMatrix b, hmat, Matrix.det_fromBlocks_zero₂₁,
    LinearMap.det_toMatrix b₁, LinearMap.det_toMatrix b₂, ← Algebra.norm_apply,
    ← Algebra.norm_apply, Algebra.norm_self, MonoidHom.id_apply, mul_comm]

/-- **Extending a full set of sections across a principal section kernel.** Suppose `B'` is finite
free over `A`, `σ : B →ₐ[A] A`, `π : B →ₐ[A] B'` is surjective, `ker σ = (u)` and `ker π = Ann(u)`.
If `s'` is a full set of sections of `B'` over `A`, then adjoining `σ` to `(s' i).comp π` produces
a full set of sections of `B` over `A`. -/
theorem IsFullSetOfSections.optionElim_of_ker_span_singleton {ι : Type*} [Fintype ι]
    [Module.Free A B'] [Module.Finite A B'] {σ : B →ₐ[A] A} {π : B →ₐ[A] B'}
    (hπ : Function.Surjective π) {u : B} (hσ : RingHom.ker σ = Ideal.span {u})
    (hkerπ : RingHom.ker π = (Ideal.span {u}).annihilator) {s' : ι → B' →ₐ[A] A}
    (hs' : IsFullSetOfSections s') :
    IsFullSetOfSections (fun o : Option ι ↦ o.elim σ fun i ↦ (s' i).comp π) := by
  rw [isFullSetOfSections_iff]
  intro T _ _ _ f
  rw [Algebra.norm_eq_mul_of_ker_span_singleton hπ hσ hkerπ T f, hs'.norm_eq T,
    Fintype.prod_option]
  refine congrArg (σ.sectionBaseChange T f * ·) (Finset.prod_congr rfl fun i _ ↦ ?_)
  induction f using TensorProduct.inductionOn with
  | tmul t b => simp [AlgHom.sectionBaseChange_tmul]
  | add x y hx hy => simp [map_add, hx, hy]

end PrincipalKernel

end TauCeti
