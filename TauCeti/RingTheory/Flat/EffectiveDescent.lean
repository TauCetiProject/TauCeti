/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import TauCeti.RingTheory.TensorProduct.Maps

/-!
# Effective faithfully flat descent for algebras

Let `S` be an `R`-algebra. A descent datum on an `S`-algebra `B` relative to `R → S` is recorded
as an `S`-algebra map `θ : B → S ⊗[R] B` (the *coaction*) which is a section of the
multiplication map `S ⊗[R] B → B` and satisfies the coassociativity condition
`(id ⊗ θ) ∘ θ = (id ⊗ (1 ⊗ ·)) ∘ θ` in `S ⊗[R] (S ⊗[R] B)`. This is the classical
isomorphism-plus-cocycle formulation in another guise: an isomorphism of
`S ⊗[R] S`-algebras `φ : B ⊗[R] S ≅ S ⊗[R] B` corresponds to `θ b = φ (b ⊗ 1)`, the
normalisation of `φ` on the diagonal to the counit equation, and the cocycle condition on
`S ⊗[R] S ⊗[R] S` to coassociativity. Forgetting the multiplication, a descent datum is in
particular a coalgebra for the comonad `S ⊗[R] -` on `S`-modules (the module form of descent,
behind Mathlib's `comonadicExtendScalars`); the algebra structure adds the requirement that the
coaction be an `S`-algebra map.

Since `Spec` is an anti-equivalence between commutative `R`-algebras and affine schemes over
`Spec R`, the results below are effective descent for affine schemes along a faithfully flat
morphism `Spec S → Spec R` of affine schemes:

* `TauCeti.Algebra.DescentDatum.baseChangeEquiv` (effectivity): if `S` is flat over `R`, the
  descended algebra `D.descended = {b | θ b = 1 ⊗ b}` satisfies `S ⊗[R] D.descended ≃ B`, and
  `coaction_baseChangeEquiv` identifies `θ` with the canonical datum on `S ⊗[R] D.descended`.
* `TauCeti.Algebra.DescentDatum.descended_baseChange`: if `S` is faithfully flat over `R`, the
  canonical datum on `S ⊗[R] A` descends to (the image of) `A`.
* `TauCeti.Algebra.DescentDatum.equivDescended` (uniqueness): if `S` is faithfully flat over `R`,
  every `R`-algebra `A` with `S ⊗[R] A ≃ B` compatibly with the descent data is isomorphic to
  `D.descended`.

The faithfully flat input is the exactness of the Amitsur sequence
`M → S ⊗[R] M ⇉ S ⊗[R] (S ⊗[R] M)` for an arbitrary `R`-module `M`
(`Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one`), which generalises Mathlib's
`Algebra.IsEffective.of_faithfullyFlat` (the case `M = R`, after identifying `S ⊗[R] R` with
`S`).

## References

* A. Grothendieck, *Revêtements étales et groupe fondamental* (SGA 1), Exposé VIII,
  Théorème 2.1 (effective descent for affine morphisms along faithfully flat quasi-compact
  morphisms).
* The Stacks Project, Chapter *Descent*, Section *Descent for modules* (the Amitsur complex
  argument used here).
-/

public section

open TensorProduct

section Amitsur

variable {R : Type*} (S : Type*) (M : Type*) [CommRing R] [Ring S] [Algebra R S]
  [AddCommGroup M] [Module R M]

/-- **Amitsur exactness.** If `S` is a faithfully flat `R`-algebra, then for every `R`-module
`M` the sequence `M → S ⊗[R] M → S ⊗[R] (S ⊗[R] M)`, with maps `m ↦ 1 ⊗ m` and
`s ⊗ m ↦ s ⊗ (1 ⊗ m) - 1 ⊗ (s ⊗ m)`, is exact. -/
theorem Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one [Module.FaithfullyFlat R S] :
    Function.Exact (TensorProduct.mk R S M 1)
      ((TensorProduct.mk R S M 1).lTensor S - TensorProduct.mk R S (S ⊗[R] M) 1) := by
  set d := (TensorProduct.mk R S M 1).lTensor S - TensorProduct.mk R S (S ⊗[R] M) 1
  have hd : d ∘ₗ TensorProduct.mk R S M 1 = 0 := by
    ext m
    simp [d]
  -- After base change to `S`, the action `s ⊗ x ↦ s • x` of `S` on the left factor (multiplying
  -- the first two factors) is a contracting homotopy.
  let h := TensorProduct.lift (Algebra.lsmul R R (A := S) (S ⊗[R] M)).toLinearMap
  let h' := TensorProduct.lift (Algebra.lsmul R R (A := S) (S ⊗[R] (S ⊗[R] M))).toLinearMap
  have key : h' ∘ₗ d.lTensor S = (TensorProduct.mk R S M 1).lTensor S ∘ₗ h - LinearMap.id := by
    ext s t m
    simp [d, h, h', smul_tmul']
  refine Module.FaithfullyFlat.lTensor_reflects_exact R S _ _ fun y ↦ ⟨fun hy ↦ ?_, ?_⟩
  · refine ⟨h y, ?_⟩
    have := congr($key y)
    simp only [LinearMap.comp_apply, hy, map_zero, LinearMap.sub_apply, LinearMap.id_apply] at this
    exact (sub_eq_zero.mp this.symm)
  · rintro ⟨x, rfl⟩
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, hd, LinearMap.lTensor_zero,
      LinearMap.zero_apply]

end Amitsur

namespace TauCeti

namespace Algebra

variable (R S B : Type*) [CommRing R] [CommRing S] [Algebra R S]
  [Ring B] [Algebra R B] [Algebra S B] [IsScalarTower R S B]

/-- A descent datum on the `S`-algebra `B` relative to `R → S`, in coalgebra form: an
`S`-algebra map `coaction : B → S ⊗[R] B` (where `S` acts on the left factor) which is a section
of the multiplication map `s ⊗ b ↦ s • b` and is coassociative. In terms of the classical
gluing isomorphism `φ : B ⊗[R] S ≅ S ⊗[R] B` one has `coaction b = φ (b ⊗ 1)`;
`counit_coaction` is the normalisation of `φ` and `coassoc` is the cocycle condition. -/
@[ext]
structure DescentDatum where
  /-- The coaction `B → S ⊗[R] B`, linear over `S` acting on the left factor. -/
  coaction : B →ₐ[S] S ⊗[R] B
  /-- The coaction is a section of the multiplication map `S ⊗[R] B → B`. -/
  counit_coaction (b : B) :
    Algebra.TensorProduct.lift (Algebra.ofId S B) (AlgHom.id R B)
      (fun s b ↦ by rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left s _)
      (coaction b) = b
  /-- The cocycle condition: `(id ⊗ θ) ∘ θ = (id ⊗ (1 ⊗ ·)) ∘ θ`. -/
  coassoc (b : B) :
    Algebra.TensorProduct.map (AlgHom.id R S) (coaction.restrictScalars R) (coaction b) =
      Algebra.TensorProduct.map (AlgHom.id R S) Algebra.TensorProduct.includeRight (coaction b)

namespace DescentDatum

variable {R S B} (D : DescentDatum R S B)

/-- The coaction of a descent datum is injective, being a section of the multiplication map. -/
theorem coaction_injective : Function.Injective D.coaction :=
  Function.LeftInverse.injective D.counit_coaction

/-- The algebra descended from a descent datum: the `R`-subalgebra of elements `b` with
`coaction b = 1 ⊗ b`. -/
def descended : Subalgebra R B :=
  AlgHom.equalizer (D.coaction.restrictScalars R) Algebra.TensorProduct.includeRight

@[simp]
theorem mem_descended_iff {b : B} : b ∈ D.descended ↔ D.coaction b = 1 ⊗ₜ b :=
  Iff.rfl

/-- The comparison map `S ⊗[R] D.descended → B`, `s ⊗ a ↦ s • a`. -/
private noncomputable def baseChangeHom : S ⊗[R] D.descended →ₐ[S] B :=
  Algebra.TensorProduct.lift (Algebra.ofId S B) D.descended.val fun s a ↦ by
    rw [Algebra.ofId_apply]; exact Algebra.commute_algebraMap_left s _

private theorem coaction_baseChangeHom (x : S ⊗[R] D.descended) :
    D.coaction (D.baseChangeHom x) =
      Algebra.TensorProduct.map (AlgHom.id R S) D.descended.val x := by
  induction x using TensorProduct.inductionOn with
  | tmul s a =>
    have ha : D.coaction a = 1 ⊗ₜ (a : B) := a.2
    rw [baseChangeHom, Algebra.TensorProduct.lift_tmul]
    simp [ha, Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
  | add x y hx hy => simp [hx, hy]

private theorem baseChangeHom_bijective [Module.Flat R S] :
    Function.Bijective D.baseChangeHom := by
  have hθ : ∀ x : S ⊗[R] D.descended,
      D.coaction (D.baseChangeHom x) = (D.descended.val.toLinearMap).lTensor S x :=
    fun x ↦ by rw [coaction_baseChangeHom, AlgHom.lTensor_toLinearMap_apply]
  refine ⟨fun x y hxy ↦ ?_, fun b ↦ ?_⟩
  · refine Module.Flat.lTensor_preserves_injective_linearMap D.descended.val.toLinearMap
      (fun _ _ h ↦ Subtype.ext h) ?_
    rw [← hθ, ← hθ, hxy]
  -- The coaction of `b` is killed by the base change of the equalizer pair, by coassociativity.
  have hexact : Function.Exact D.descended.val.toLinearMap
      ((D.coaction.restrictScalars R).toLinearMap -
        (Algebra.TensorProduct.includeRight : B →ₐ[R] S ⊗[R] B).toLinearMap) := fun b ↦
    ⟨fun h ↦ ⟨⟨b, sub_eq_zero.mp h⟩, rfl⟩, by rintro ⟨a, rfl⟩; exact sub_eq_zero.mpr a.2⟩
  obtain ⟨x, hx⟩ := ((Module.Flat.lTensor_exact S hexact) (D.coaction b)).mp <| by
    rw [LinearMap.lTensor_sub, LinearMap.sub_apply, AlgHom.lTensor_toLinearMap_apply,
      AlgHom.lTensor_toLinearMap_apply, D.coassoc, sub_self]
  exact ⟨x, D.coaction_injective (by rw [hθ, hx])⟩

/-- **Effectivity of flat descent for algebras.** If `S` is flat over `R`, every descent datum
on `B` is effective: the descended algebra base changes back to `B`, via `s ⊗ a ↦ s • a`. -/
noncomputable def baseChangeEquiv [Module.Flat R S] : S ⊗[R] D.descended ≃ₐ[S] B :=
  AlgEquiv.ofBijective D.baseChangeHom D.baseChangeHom_bijective

@[simp]
theorem baseChangeEquiv_tmul [Module.Flat R S] (s : S) (a : D.descended) :
    D.baseChangeEquiv (s ⊗ₜ a) = s • (a : B) := by
  simp [baseChangeEquiv, baseChangeHom, Algebra.smul_def]

/-- `baseChangeEquiv` is compatible with the descent data: the coaction of `D` sends
`s • a`, for `a` in the descended algebra, to `s ⊗ a`. Equivalently, `baseChangeEquiv`
carries the canonical descent datum `s ⊗ a ↦ s ⊗ (1 ⊗ a)` on `S ⊗[R] D.descended` to `D`. -/
theorem coaction_baseChangeEquiv [Module.Flat R S] (x : S ⊗[R] D.descended) :
    D.coaction (D.baseChangeEquiv x) =
      Algebra.TensorProduct.map (AlgHom.id R S) D.descended.val x :=
  D.coaction_baseChangeHom x

variable (R S) in
/-- The canonical descent datum on `S ⊗[R] A`, with coaction `s ⊗ a ↦ s ⊗ (1 ⊗ a)`. -/
noncomputable def baseChange (A : Type*) [Ring A] [Algebra R A] :
    DescentDatum R S (S ⊗[R] A) where
  coaction := Algebra.TensorProduct.map (AlgHom.id S S) Algebra.TensorProduct.includeRight
  counit_coaction x := by
    induction x using TensorProduct.inductionOn with
    | tmul s a =>
      simp [Algebra.TensorProduct.algebraMap_apply, Algebra.TensorProduct.tmul_mul_tmul]
    | add x y hx hy => simp only [map_add, hx, hy]
  coassoc x := by
    induction x using TensorProduct.inductionOn with
    | tmul s a => simp
    | add x y hx hy => simp only [map_add, hx, hy]

@[simp]
theorem baseChange_coaction_tmul {A : Type*} [Ring A] [Algebra R A] (s : S) (a : A) :
    (baseChange R S A).coaction (s ⊗ₜ a) = s ⊗ₜ (1 ⊗ₜ a) :=
  (rfl)

/-- If `S` is faithfully flat over `R`, the canonical descent datum on `S ⊗[R] A` descends to
the image of `A`, i.e. the elements of the form `1 ⊗ a`. -/
theorem descended_baseChange [Module.FaithfullyFlat R S] (A : Type*) [Ring A] [Algebra R A] :
    (baseChange R S A).descended = (Algebra.TensorProduct.includeRight : A →ₐ[R] S ⊗[R] A).range
    := by
  ext x
  have hθ : (baseChange R S A).coaction x = (TensorProduct.mk R S A 1).lTensor S x := by
    induction x using TensorProduct.inductionOn with
    | tmul s a => simp
    | add x y hx hy => simp only [map_add, hx, hy]
  rw [mem_descended_iff, hθ, ← sub_eq_zero, AlgHom.mem_range]
  exact (Module.FaithfullyFlat.exact_mk_one_lTensor_sub_mk_one S A x).trans
    (by simp [eq_comm])

/-- **Uniqueness of descent.** If `S` is faithfully flat over `R`, `A` is an `R`-algebra and
`e : S ⊗[R] A ≃ B` is an `S`-algebra isomorphism carrying `1 ⊗ A` into the descended algebra
(equivalently, carrying the canonical descent datum on `S ⊗[R] A` to `D`), then
`a ↦ e (1 ⊗ a)` is an isomorphism of `A` onto `D.descended`. -/
noncomputable def equivDescended [Module.FaithfullyFlat R S] {A : Type*} [Ring A] [Algebra R A]
    (e : S ⊗[R] A ≃ₐ[S] B) (he : ∀ a : A, e (1 ⊗ₜ a) ∈ D.descended) : A ≃ₐ[R] D.descended :=
  AlgEquiv.ofBijective
    (((e.toAlgHom.restrictScalars R).comp Algebra.TensorProduct.includeRight).codRestrict _
      fun a ↦ by simpa using he a)
    (by
      refine ⟨fun a a' h ↦ ?_, fun ⟨b, hb⟩ ↦ ?_⟩
      · have h' : (1 : S) ⊗ₜ[R] (a - a') = 0 := by
          rw [tmul_sub, sub_eq_zero]
          exact e.injective congr($h.1)
        simpa [sub_eq_zero] using h'
      -- The coaction of `D` is the transport of the canonical coaction along `e`.
      have hcompat : ∀ x, D.coaction (e x) =
          Algebra.TensorProduct.map (AlgHom.id R S) (e.toAlgHom.restrictScalars R)
            ((baseChange R S A).coaction x) := by
        intro x
        induction x using TensorProduct.inductionOn with
        | tmul s a =>
          have h1 : e (s ⊗ₜ a) = s • e (1 ⊗ₜ a) := by
            rw [← map_smul, smul_tmul', smul_eq_mul, mul_one]
          simp [h1, (mem_descended_iff _).mp (he a), smul_tmul']
        | add x y hx hy => simp only [map_add, hx, hy]
      have hmem : e.symm b ∈ (baseChange R S A).descended := by
        refine (mem_descended_iff _).mpr ?_
        have hinj := (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[R] S)
          (e.restrictScalars R)).injective
        apply hinj
        have := hcompat (e.symm b)
        simp only [AlgEquiv.apply_symm_apply] at this
        simpa [← this] using hb
      rw [descended_baseChange] at hmem
      obtain ⟨a, ha⟩ := hmem
      have ha' : (1 : S) ⊗ₜ[R] a = e.symm b := by simpa using ha
      exact ⟨a, Subtype.ext <| by simp [ha']⟩)

@[simp]
theorem coe_equivDescended_apply [Module.FaithfullyFlat R S] {A : Type*} [Ring A] [Algebra R A]
    (e : S ⊗[R] A ≃ₐ[S] B) (he : ∀ a : A, e (1 ⊗ₜ a) ∈ D.descended) (a : A) :
    (D.equivDescended e he a : B) = e (1 ⊗ₜ a) :=
  (rfl)

end DescentDatum

end Algebra

end TauCeti
