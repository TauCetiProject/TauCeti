/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.LinearAlgebra.Charpoly.ToMatrix
public import Mathlib.RingTheory.Polynomial.Basic
public import Mathlib.RingTheory.TensorProduct.Pi
public import TauCeti.RingTheory.NormTrace.BaseChange
public import TauCeti.RingTheory.NormTrace.Pi
public import TauCeti.RingTheory.NormTrace.Prod
public import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Full sets of sections

Let `B` be a commutative `A`-algebra, finite and locally free as an `A`-module, so that
`Z = Spec B → Spec A` is finite locally free. An `A`-algebra map `B →ₐ[A] A` is a section of
`Z`. A family of sections `s : ι → (B →ₐ[A] A)` is a *full set of sections* (Katz–Mazur §1.8)
when, after every base change `A → T`, the norm of every function on `Z_T` is the product of its
values at the sections:

  `Norm_{T ⊗[A] B / T} (f) = ∏ i, sᵢ(f)`  for all `f ∈ T ⊗[A] B`.

The quantification over base changes is part of the definition. Full sets of sections are how
Katz and Mazur express, over an arbitrary base, that a finite flat scheme "consists of" given
points counted with multiplicity: Drinfeld level structures on elliptic curves are defined by
asking that the points of a homomorphism `(ℤ/N)² → E[N]`, or the multiples of a point, form a
full set of sections of a finite locally free subgroup scheme.

## Main definitions

* `TauCeti.IsFullSetOfSections s`: the family `s` is a full set of sections of `B` over `A`.
  The norm is tested on the base changes `T ⊗[A] B` which are free over `T`; when `B` is free over
  `A` this is every base change, and every finite projective `B` is free Zariski-locally on
  `Spec A`.

## Main results

Throughout, `B` is free of finite rank over `A`.

* `TauCeti.IsFullSetOfSections.norm_eq`: the defining identity holds for test algebras in every
  universe.
* `TauCeti.isFullSetOfSections_iff_norm_eq_prod`: the reduction to the universal case
  (Katz–Mazur, proof of 1.9.1). For a basis `b` of `B` indexed by `κ`, `s` is a full set of
  sections if and only if the norm form factors into linear forms,
  `Norm (∑ j, Xⱼ ⊗ bⱼ) = ∏ i, ∑ j, sᵢ(bⱼ) • Xⱼ` in `MvPolynomial κ A`.
* `TauCeti.isFullSetOfSections_iff_charpoly`: the characteristic-polynomial formulation
  (Katz–Mazur 1.8.2).
* `TauCeti.IsFullSetOfSections.baseChange`, `TauCeti.IsFullSetOfSections.of_baseChange` and
  `TauCeti.isFullSetOfSections_baseChange_iff`: full sets of sections are stable under arbitrary
  base change and descend along injective ring maps, in particular along faithfully flat ones.
* `TauCeti.IsFullSetOfSections.card_eq_finrank`: over a nontrivial ring, a full set of sections
  has exactly `rank B` members.
* `TauCeti.isFullSetOfSections_evalAlgHom`: the coordinate projections of `ι → A`, the sections
  of the constant scheme `⨆_{i ∈ ι} Spec A`, form a full set of sections.
* `TauCeti.IsFullSetOfSections.prod`: full sets of sections of `B₁` and `B₂` together form one of
  `B₁ × B₂` (Katz–Mazur 1.8.4).

## References

* N. M. Katz, B. Mazur, *Arithmetic Moduli of Elliptic Curves*, Annals of Mathematics Studies
  108, Princeton University Press, 1985, §§1.8–1.9.
-/

public section

open TensorProduct MvPolynomial

namespace TauCeti

universe u v w

variable {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
variable {ι : Type*} [Fintype ι]

/-- A family `s` of `A`-algebra maps `B →ₐ[A] A`, that is, of sections of `Spec B → Spec A`, is a
*full set of sections* (Katz–Mazur §1.8) if after every base change `A → T` the norm of every
`f ∈ T ⊗[A] B` over `T` is the product `∏ i, sᵢ(f)` of the values of `f` at the base-changed
sections. Norms are taken on the base changes `T ⊗[A] B` which are free over `T`, where
`Algebra.norm` is the determinant of multiplication. -/
def IsFullSetOfSections (s : ι → B →ₐ[A] A) : Prop :=
  ∀ (T : Type u) [CommRing T] [Algebra A T] [Module.Free T (T ⊗[A] B)] (f : T ⊗[A] B),
    Algebra.norm T f = ∏ i, (s i).sectionBaseChange T f

variable {s : ι → B →ₐ[A] A}

/-- Unfolding `IsFullSetOfSections`: the norm identity holds on every base change `T ⊗[A] B` which
is free over `T`, for `T` in the universe of `A`. -/
theorem isFullSetOfSections_iff : IsFullSetOfSections s ↔
    ∀ (T : Type u) [CommRing T] [Algebra A T] [Module.Free T (T ⊗[A] B)] (f : T ⊗[A] B),
      Algebra.norm T f = ∏ i, (s i).sectionBaseChange T f :=
  Iff.rfl

/-- The base change of a section `s` to `MvPolynomial κ A` takes the generic element
`∑ j, Xⱼ ⊗ bⱼ` to the linear form `∑ j, s(bⱼ) • Xⱼ`. -/
private theorem sectionBaseChange_generic (s : B →ₐ[A] A) {κ : Type*} [Fintype κ]
    (b : Module.Basis κ A B) :
    s.sectionBaseChange (MvPolynomial κ A) (∑ j, (X j : MvPolynomial κ A) ⊗ₜ[A] b j) =
      ∑ j, s (b j) • (X j : MvPolynomial κ A) := by
  simp [Algebra.smul_def, mul_comm]

section Free

variable [Module.Free A B] [Module.Finite A B]

/-- If the norm form of `B` in a basis `b` factors as `∏ i, ∑ j, sᵢ(bⱼ) • Xⱼ`, then the norm on
every base change `T ⊗[A] B` is the product of the values at the sections: write
`f = ∑ j, cⱼ ⊗ bⱼ` and specialize `Xⱼ ↦ cⱼ`. -/
private theorem norm_eq_prod_of_generic {κ : Type*} [Fintype κ] (b : Module.Basis κ A B)
    (h : Algebra.norm (MvPolynomial κ A) (∑ j, (X j : MvPolynomial κ A) ⊗ₜ[A] b j) =
      ∏ i, ∑ j, s i (b j) • (X j : MvPolynomial κ A))
    (T : Type w) [CommRing T] [Algebra A T] (f : T ⊗[A] B) :
    Algebra.norm T f = ∏ i, (s i).sectionBaseChange T f := by
  classical
  set c := (Algebra.TensorProduct.basis T b).repr f
  have hf : Algebra.TensorProduct.rTensor B (aeval (fun j ↦ c j))
      (∑ j, (X j : MvPolynomial κ A) ⊗ₜ[A] b j) = f := by
    conv_rhs => rw [← (Algebra.TensorProduct.basis T b).sum_repr f]
    simp [c, TensorProduct.smul_tmul']
  rw [← hf, Algebra.norm_rTensor, h, map_prod]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [AlgHom.sectionBaseChange_rTensor, sectionBaseChange_generic]

/-- The defining identity of a full set of sections holds after base change to a commutative
`A`-algebra `T` in any universe. -/
theorem IsFullSetOfSections.norm_eq (h : IsFullSetOfSections s) (T : Type w) [CommRing T]
    [Algebra A T] (f : T ⊗[A] B) :
    Algebra.norm T f = ∏ i, (s i).sectionBaseChange T f :=
  norm_eq_prod_of_generic ((Module.Free.chooseBasis A B).reindex (Fintype.equivFin _))
    ((h _ _).trans (Finset.prod_congr rfl fun _ _ ↦ sectionBaseChange_generic _ _)) T f

/-- **Reduction to the universal case** (Katz–Mazur, proof of 1.9.1). For a basis `b` of `B`
indexed by `κ`, a family of sections `s` is a full set of sections if and only if the norm of the
generic element `∑ j, Xⱼ ⊗ bⱼ` of `MvPolynomial κ A ⊗[A] B` is the product of the linear forms
`∑ j, sᵢ(bⱼ) • Xⱼ`. -/
theorem isFullSetOfSections_iff_norm_eq_prod {κ : Type*} [Fintype κ] (b : Module.Basis κ A B) :
    IsFullSetOfSections s ↔
      Algebra.norm (MvPolynomial κ A) (∑ j, (X j : MvPolynomial κ A) ⊗ₜ[A] b j) =
        ∏ i, ∑ j, s i (b j) • (X j : MvPolynomial κ A) :=
  ⟨fun h ↦ (h.norm_eq _ _).trans (Finset.prod_congr rfl fun _ _ ↦ sectionBaseChange_generic _ _),
    fun h T _ _ _ f ↦ norm_eq_prod_of_generic b h T f⟩

omit [Module.Free A B] [Module.Finite A B] in
/-- The generic element of `T ⊗[A] B` over `T`, in the basis induced by `b`, has the same norm as
the image of the generic element of `B` in `MvPolynomial κ T ⊗[A] B`. -/
private theorem norm_generic_baseChange {κ : Type*} [Fintype κ] (b : Module.Basis κ A B)
    (T : Type w) [CommRing T] [Algebra A T] :
    Algebra.norm (MvPolynomial κ T)
        (∑ j, (X j : MvPolynomial κ T) ⊗ₜ[T] Algebra.TensorProduct.basis T b j) =
      Algebra.norm (MvPolynomial κ T) (Algebra.TensorProduct.rTensor B
        (mapAlgHom (Algebra.ofId A T)) (∑ j, (X j : MvPolynomial κ A) ⊗ₜ[A] b j)) := by
  rw [← Algebra.norm_eq_of_algEquiv
    (Algebra.TensorProduct.cancelBaseChange A T (MvPolynomial κ T) (MvPolynomial κ T) B)]
  simp

/-- A full set of sections remains one after an arbitrary base change `A → T`. -/
theorem IsFullSetOfSections.baseChange (h : IsFullSetOfSections s) (T : Type w) [CommRing T]
    [Algebra A T] : IsFullSetOfSections fun i ↦ (s i).sectionBaseChange T := by
  let b := Module.Free.chooseBasis A B
  rw [isFullSetOfSections_iff_norm_eq_prod (Algebra.TensorProduct.basis T b),
    norm_generic_baseChange, Algebra.norm_rTensor, (isFullSetOfSections_iff_norm_eq_prod b).1 h]
  simp [map_prod]

/-- Being a full set of sections descends along an injective ring map `A → T`, in particular
along a faithfully flat one. -/
theorem IsFullSetOfSections.of_baseChange {T : Type w} [CommRing T] [Algebra A T]
    (hT : Function.Injective (algebraMap A T))
    (h : IsFullSetOfSections fun i ↦ (s i).sectionBaseChange T) : IsFullSetOfSections s := by
  let b := Module.Free.chooseBasis A B
  rw [isFullSetOfSections_iff_norm_eq_prod b]
  apply MvPolynomial.map_injective _ hT
  have := (isFullSetOfSections_iff_norm_eq_prod (Algebra.TensorProduct.basis T b)).1 h
  rw [norm_generic_baseChange, Algebra.norm_rTensor] at this
  simpa [map_prod, Algebra.smul_def] using this

/-- Over a base change which is injective, being a full set of sections can be checked after the
base change. -/
theorem isFullSetOfSections_baseChange_iff {T : Type w} [CommRing T] [Algebra A T]
    (hT : Function.Injective (algebraMap A T)) :
    (IsFullSetOfSections fun i ↦ (s i).sectionBaseChange T) ↔ IsFullSetOfSections s :=
  ⟨.of_baseChange hT, fun h ↦ h.baseChange T⟩

/-- Over a nontrivial ring, a full set of sections has as many members as the rank of `B`. -/
theorem IsFullSetOfSections.card_eq_finrank [Nontrivial A] (h : IsFullSetOfSections s) :
    Fintype.card ι = Module.finrank A B := by
  have := h.norm_eq (Polynomial A) (algebraMap (Polynomial A) _ Polynomial.X)
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange] at this
  simpa using congrArg Polynomial.natDegree this.symm

/-- The characteristic polynomial of multiplication by `f` on a base change of `B` by a full set
of sections is `∏ i, (X - sᵢ(f))`, for test algebras in any universe. -/
theorem IsFullSetOfSections.charpoly_eq (h : IsFullSetOfSections s) (T : Type w) [CommRing T]
    [Algebra A T] (f : T ⊗[A] B) :
    (Algebra.lmul T (T ⊗[A] B) f).charpoly =
      ∏ i, (Polynomial.X - Polynomial.C ((s i).sectionBaseChange T f)) := by
  rw [Algebra.charpoly_lmul_eq_norm, h.norm_eq]
  simp [Polynomial.algebraMap_eq]

/-- **Characteristic-polynomial formulation** (Katz–Mazur 1.8.2). A family of sections `s` is a
full set of sections if and only if after every base change `A → T` the characteristic polynomial
of multiplication by every `f ∈ T ⊗[A] B` is `∏ i, (X - sᵢ(f))`. -/
theorem isFullSetOfSections_iff_charpoly :
    IsFullSetOfSections s ↔ ∀ (T : Type u) [CommRing T] [Algebra A T] (f : T ⊗[A] B),
      (Algebra.lmul T (T ⊗[A] B) f).charpoly =
        ∏ i, (Polynomial.X - Polynomial.C ((s i).sectionBaseChange T f)) := by
  refine ⟨fun h T _ _ f ↦ h.charpoly_eq T f, fun h ↦ ?_⟩
  intro T _ _ _ f
  rcases subsingleton_or_nontrivial T with _ | _
  · exact Subsingleton.elim _ _
  have hdeg := congrArg Polynomial.natDegree (h T f)
  rw [LinearMap.charpoly_natDegree, Polynomial.natDegree_finsetProd_X_sub_C_eq_card,
    Finset.card_univ] at hdeg
  rw [Algebra.norm_apply, LinearMap.det_eq_sign_charpoly_coeff, h T f,
    Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod, hdeg]
  simp [Finset.prod_neg, ← mul_assoc, ← pow_add]

end Free

/-- The coordinate projections `ι → A`, the sections of the constant finite scheme
`⨆_{i ∈ ι} Spec A`, form a full set of sections. -/
theorem isFullSetOfSections_evalAlgHom :
    IsFullSetOfSections fun i ↦ Pi.evalAlgHom A (fun _ : ι ↦ A) i := by
  classical
  intro T _ _ _ f
  rw [← Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.piScalarRight A T T ι),
    Algebra.norm_pi]
  refine Finset.prod_congr rfl fun i _ ↦ ?_
  rw [Algebra.norm_self, MonoidHom.id_apply]
  induction f using TensorProduct.inductionOn with
  | tmul t y => simp [Algebra.smul_def, mul_comm]
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]

/-- **Disjoint unions** (Katz–Mazur 1.8.4). If `s₁` and `s₂` are full sets of sections of `B₁`
and `B₂`, then their composites with the two projections together form a full set of sections of
`B₁ × B₂`. -/
theorem IsFullSetOfSections.prod {B₁ B₂ : Type*} [CommRing B₁] [Algebra A B₁] [CommRing B₂]
    [Algebra A B₂] [Module.Free A B₁] [Module.Finite A B₁] [Module.Free A B₂]
    [Module.Finite A B₂] {ι₁ ι₂ : Type*} [Fintype ι₁] [Fintype ι₂] {s₁ : ι₁ → B₁ →ₐ[A] A}
    {s₂ : ι₂ → B₂ →ₐ[A] A} (h₁ : IsFullSetOfSections s₁) (h₂ : IsFullSetOfSections s₂) :
    IsFullSetOfSections (Sum.elim (fun i ↦ (s₁ i).comp (AlgHom.fst A B₁ B₂))
      fun i ↦ (s₂ i).comp (AlgHom.snd A B₁ B₂)) := by
  intro T _ _ _ f
  rw [← Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.prodRight A T T B₁ B₂),
    Algebra.norm_prod, h₁.norm_eq, h₂.norm_eq, Fintype.prod_sum_type]
  congr 1 <;> refine Finset.prod_congr rfl fun i _ ↦ ?_ <;>
  induction f using TensorProduct.inductionOn with
  | tmul t y => simp
  | add x y hx hy => simp only [map_add, Prod.fst_add, Prod.snd_add, hx, hy]

end TauCeti
