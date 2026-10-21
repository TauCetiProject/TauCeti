/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Etale.Descent
public import Mathlib.RingTheory.Etale.Pi
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.RingTheory.Idempotents
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.TensorProduct.Pi

import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Localization.Away.Lemmas
import TauCeti.RingTheory.Etale.Idempotent
import TauCeti.RingTheory.Idempotents.Refinement
import TauCeti.RingTheory.Spectrum.Prime.FreeLocus

/-!
# Equalizers of finite étale algebras

The equalizer of two algebra maps `f g : A →ₐ[R] B` between finite étale `R`-algebras is a finite
étale `R`-algebra (`AlgHom.etale_equalizer`, `AlgHom.finite_equalizer`). In particular, the
invariants of a finite étale algebra under a finite monoid acting by algebra endomorphisms form a
finite étale algebra (`FixedPoints.etale_subalgebra`, `FixedPoints.finite_subalgebra`).
Geometrically, the affine coequalizer of two morphisms of finite étale `Spec R`-schemes, and the
invariant quotient of a finite étale `Spec R`-scheme by a finite group, are again finite étale.
These are the coequalizers and the quotients by finite groups required of finite étale covers by
the axioms of a Galois category.

## Main results

* `AlgHom.etale_equalizer`, `AlgHom.finite_equalizer`: equalizers of finite étale algebras are
  finite étale.
* `FixedPoints.etale_subalgebra`, `FixedPoints.finite_subalgebra`: invariants of a finite étale
  algebra under a finite monoid are finite étale.
* `Algebra.Etale.of_completeOrthogonalIdempotents` and
  `Module.Finite.of_completeOrthogonalIdempotents`: an algebra is étale, respectively finite, if
  its base change to every component of a complete orthogonal family of idempotents of the base
  is.

## Implementation notes

The proof reduces to split algebras in three steps.

* Over a split base, an algebra map `φ : (ι → T) →ₐ[T] (κ → T)` has idempotent matrix entries
  `φ (Pi.single i 1) j`. Over the component of each atom of the Boolean algebra they generate
  (`CompleteOrthogonalIdempotents.prod_ite`), every entry is `0` or `1`, so `φ` is induced by a map
  `κ → ι`, and the equalizer of two such maps is the algebra of functions on a quotient of `ι`.
* If `A` and `B` have constant ranks, they both split after a faithfully flat finite étale base
  change (`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`). Flat base change commutes with
  equalizers (`AlgHom.tensorEqualizerEquiv`), and finite étaleness descends along faithfully flat
  maps.
* In general the ranks are locally constant, and the atoms of the idempotents cutting out their
  fibres decompose the base into components where both ranks are constant.

The main results take `R`, `A` and `B` in one universe, as
`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale` does.

## References

* H. W. Lenstra, *Galois theory for schemes*, Section 5.
* The Stacks Project, Section 58.5 (tag 0BL8), *Finite étale covers of schemes*.
-/

public section

open TensorProduct

universe u

section Decomposition

variable {T X : Type*} [CommRing T] [CommRing X] [Algebra T X]

/-- A complete orthogonal family of idempotents `f i` of `T` splits every `T`-algebra `X` into
the product of its base changes to the components `T ⧸ (1 - f i)`. -/
private noncomputable def piTensorQuotientEquiv {ι : Type*} [Fintype ι] [DecidableEq ι]
    {f : ι → T} (hf : CompleteOrthogonalIdempotents f) :
    X ≃ₐ[T] Π i, (T ⧸ Ideal.span {1 - f i}) ⊗[T] X :=
  (Algebra.TensorProduct.lid T X).symm.trans <|
    (Algebra.TensorProduct.congr
      (AlgEquiv.ofBijective (AlgHom.pi fun _ ↦ Ideal.Quotient.mkₐ T _) hf.bijective_pi)
      AlgEquiv.refl).trans <|
    (Algebra.TensorProduct.comm T _ X).trans <|
    (Algebra.TensorProduct.piRight T T X _).trans <|
    AlgEquiv.piCongrRight fun _ ↦ Algebra.TensorProduct.comm T X _

/-- Étaleness is local for a decomposition of the base by complete orthogonal idempotents: if the
base change of `X` to every component `T ⧸ (1 - f i)` is étale, then `X` is étale over `T`. -/
theorem Algebra.Etale.of_completeOrthogonalIdempotents {ι : Type*} [Fintype ι] {f : ι → T}
    (hf : CompleteOrthogonalIdempotents f)
    (h : ∀ i, Algebra.Etale (T ⧸ Ideal.span {1 - f i}) ((T ⧸ Ideal.span {1 - f i}) ⊗[T] X)) :
    Algebra.Etale T X := by
  classical
  have (i : ι) : Algebra.Etale T ((T ⧸ Ideal.span {1 - f i}) ⊗[T] X) := by
    have := TauCeti.Algebra.Etale.quotient_span_singleton (R := T) (S := T) (hf.idem i).one_sub
    have := h i
    exact Algebra.Etale.comp T (T ⧸ Ideal.span {1 - f i}) _
  exact .of_equiv (piTensorQuotientEquiv hf).symm

/-- Module finiteness is local for a decomposition of the base by complete orthogonal
idempotents: if the base change of `X` to every component `T ⧸ (1 - f i)` is finite, then `X` is
finite over `T`. -/
theorem Module.Finite.of_completeOrthogonalIdempotents {ι : Type*} [Fintype ι] {f : ι → T}
    (hf : CompleteOrthogonalIdempotents f)
    (h : ∀ i, Module.Finite (T ⧸ Ideal.span {1 - f i}) ((T ⧸ Ideal.span {1 - f i}) ⊗[T] X)) :
    Module.Finite T X := by
  classical
  have (i : ι) : Module.Finite T ((T ⧸ Ideal.span {1 - f i}) ⊗[T] X) := by
    have := h i
    exact Module.Finite.trans (T ⧸ Ideal.span {1 - f i}) _
  exact .equiv (piTensorQuotientEquiv hf).symm.toLinearEquiv

end Decomposition

section Atoms

variable {T ι : Type*} [CommRing T] [Fintype ι] {e : ι → T}

/-- In `T ⧸ (1 - e)`, the image of `e` is `1`. -/
private theorem algebraMap_quotient_span_one_sub (e : T) :
    algebraMap T (T ⧸ Ideal.span {1 - e}) e = 1 := by
  rw [Ideal.Quotient.algebraMap_eq, ← map_one (Ideal.Quotient.mk (Ideal.span {1 - e})),
    Ideal.Quotient.eq]
  exact Ideal.mem_span_singleton'.mpr ⟨-1, by ring⟩

/-- Each factor of an atom `∏ y, (if σ y then e y else 1 - e y)` absorbs it. -/
private theorem ite_mul_prod_ite (he : ∀ i, IsIdempotentElem (e i)) (σ : ι → Bool) (x : ι) :
    (if σ x then e x else 1 - e x) * ∏ y, (if σ y then e y else 1 - e y) =
      ∏ y, (if σ y then e y else 1 - e y) := by
  have hidem : IsIdempotentElem (if σ x then e x else 1 - e x) := by
    split
    · exact he x
    · exact (he x).one_sub
  classical
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ x), ← mul_assoc, hidem.eq]

/-- A prime ideal over the component of an atom contains `e x` exactly when the atom uses
`1 - e x`. -/
private theorem notMem_iff_of_one_sub_prod_ite_mem (he : ∀ i, IsIdempotentElem (e i))
    (σ : ι → Bool) {p : Ideal T} [p.IsPrime]
    (hp : 1 - ∏ y, (if σ y then e y else 1 - e y) ∈ p) (x : ι) : e x ∉ p ↔ σ x := by
  have hF : ∏ y, (if σ y then e y else 1 - e y) ∉ p := fun h ↦
    Ideal.IsPrime.ne_top' ((Ideal.eq_top_iff_one _).mpr (by simpa using p.add_mem h hp))
  have hmul := ite_mul_prod_ite he σ x
  by_cases hσx : σ x
  · simp only [hσx, ↓reduceIte] at hmul
    exact iff_of_true (fun hx ↦ hF (hmul ▸ p.mul_mem_right _ hx)) hσx
  · simp only [hσx, Bool.false_eq_true, ↓reduceIte] at hmul
    have h1 : 1 - e x ∉ p := fun h ↦ hF (hmul ▸ p.mul_mem_right _ h)
    have h0 : e x * (1 - e x) ∈ p := by
      rw [(he x).mul_one_sub_self]
      exact p.zero_mem
    exact iff_of_false (not_not.mpr ((Ideal.IsPrime.mem_or_mem ‹_› h0).resolve_right h1)) hσx

end Atoms

namespace AlgHom

variable {R A B A' B' : Type*} [CommRing R] [CommRing A] [CommRing B] [CommRing A']
  [CommRing B'] [Algebra R A] [Algebra R B] [Algebra R A'] [Algebra R B']

/-- Transport of an equalizer along isomorphisms of the source and the target. -/
private noncomputable def equalizerCongr (eA : A ≃ₐ[R] A') (eB : B ≃ₐ[R] B')
    (f g : A →ₐ[R] B) :
    equalizer f g ≃ₐ[R]
      equalizer ((eB : B →ₐ[R] B').comp (f.comp (eA.symm : A' →ₐ[R] A)))
        ((eB : B →ₐ[R] B').comp (g.comp (eA.symm : A' →ₐ[R] A))) :=
  (eA.subalgebraMap (equalizer f g)).trans <| Subalgebra.equivOfEq _ _ <| by
    ext x
    simp only [Subalgebra.mem_map, mem_equalizer, coe_comp, Function.comp_apply,
      AlgEquiv.coe_toAlgHom, EmbeddingLike.apply_eq_iff_eq]
    exact ⟨fun ⟨y, hy, hyx⟩ ↦ hyx ▸ by simpa using hy, fun h ↦ ⟨_, h, by simp⟩⟩

section Split

variable {T : Type*} [CommRing T]

/-- An algebra map between split algebras whose matrix entries `φ (Pi.single i 1) j` are all `0`
or `1` is induced by a map of the index sets. -/
private theorem exists_apply_eq_comp_of_entries [Nontrivial T] {ι κ : Type*} [_root_.Finite ι]
    [DecidableEq ι] (φ : (ι → T) →ₐ[T] (κ → T))
    (hφ : ∀ i j, φ (Pi.single i 1) j = 0 ∨ φ (Pi.single i 1) j = 1) :
    ∃ u : κ → ι, ∀ s j, φ s j = s (u j) := by
  have := Fintype.ofFinite ι
  have hsum (j : κ) : ∑ i, φ (Pi.single i 1) j = 1 := by
    have h1 : ∑ i, (Pi.single i 1 : ι → T) = 1 := by
      simpa using Finset.univ_sum_single (1 : ι → T)
    rw [← Finset.sum_apply, ← map_sum, h1, map_one, Pi.one_apply]
  have hone (j : κ) : ∃ i, φ (Pi.single i 1) j = 1 := by
    by_contra! h
    have h0 (i : ι) : φ (Pi.single i 1) j = 0 := (hφ i j).resolve_right (h i)
    exact one_ne_zero ((hsum j).symm.trans (by simp [h0]))
  choose u hu using hone
  refine ⟨u, fun s j ↦ ?_⟩
  have hs : s = ∑ i, s i • (Pi.single i 1 : ι → T) := by
    conv_lhs => rw [← Finset.univ_sum_single s]
    simp [← Pi.single_smul']
  have hφs : φ s j = ∑ i, s i * φ (Pi.single i 1) j := by
    conv_lhs => rw [hs]
    rw [map_sum, Finset.sum_apply]
    exact Finset.sum_congr rfl fun i _ ↦ by rw [map_smul, Pi.smul_apply, smul_eq_mul]
  rw [hφs, Finset.sum_eq_single (u j) (fun i _ hi ↦ ?_) (by simp), hu j, mul_one]
  have hprod : (Pi.single i 1 : ι → T) * Pi.single (u j) 1 = 0 := by
    ext k
    by_cases hk : k = i
    · subst hk
      simp [hi]
    · simp [Pi.single_apply, hk]
  have h0 := congrFun (congrArg φ hprod) j
  rw [map_mul, map_zero, Pi.mul_apply, hu j, mul_one, Pi.zero_apply] at h0
  rw [h0, mul_zero]

/-- The equalizer of two algebra maps between split algebras whose matrix entries are all `0` or
`1` is finite étale: the maps are induced by maps `u v : κ → ι`, and the equalizer is the algebra
of functions on the quotient of `ι` by the relation identifying `u j` with `v j`. -/
private theorem etale_and_finite_equalizer_of_entries {ι κ : Type*} [_root_.Finite ι]
    [DecidableEq ι] (φ ψ : (ι → T) →ₐ[T] (κ → T))
    (hφ : ∀ i j, φ (Pi.single i 1) j = 0 ∨ φ (Pi.single i 1) j = 1)
    (hψ : ∀ i j, ψ (Pi.single i 1) j = 0 ∨ ψ (Pi.single i 1) j = 1) :
    Algebra.Etale T (equalizer φ ψ) ∧ Module.Finite T (equalizer φ ψ) := by
  cases subsingleton_or_nontrivial T
  · have : Subsingleton (equalizer φ ψ) := RingHom.codomain_trivial (algebraMap T _)
    let e : T ≃ₐ[T] equalizer φ ψ := AlgEquiv.ofBijective (Algebra.ofId T _)
      ⟨Function.injective_of_subsingleton _, Function.surjective_to_subsingleton _⟩
    exact ⟨.of_equiv e, .equiv e.toLinearEquiv⟩
  obtain ⟨u, hu⟩ := exists_apply_eq_comp_of_entries φ hφ
  obtain ⟨v, hv⟩ := exists_apply_eq_comp_of_entries ψ hψ
  let r : ι → ι → Prop := fun a b ↦ ∃ j, u j = a ∧ v j = b
  let Ψ : (Quot r → T) →ₐ[T] (ι → T) := AlgHom.pi fun i ↦ Pi.evalAlgHom T (fun _ ↦ T) (Quot.mk r i)
  have hΨ (t : Quot r → T) : Ψ t ∈ equalizer φ ψ := by
    ext j
    simpa [hu, hv, Ψ] using congrArg t (Quot.sound ⟨j, rfl, rfl⟩)
  let e : (Quot r → T) ≃ₐ[T] equalizer φ ψ := AlgEquiv.ofBijective (Ψ.codRestrict _ hΨ) <| by
    refine ⟨fun t t' h ↦ funext <| Quot.ind fun i ↦ ?_, fun ⟨s, hs⟩ ↦ ?_⟩
    · simpa [Ψ] using congrFun (congrArg Subtype.val h) i
    · refine ⟨Quot.lift s ?_, Subtype.ext (funext fun i ↦ rfl)⟩
      rintro _ _ ⟨j, rfl, rfl⟩
      simpa [hu, hv] using congrFun hs j
  exact ⟨.of_equiv e, .equiv e.toLinearEquiv⟩

/-- The matrix entries of the base change of an algebra map between split algebras are the images
of the original entries. -/
private theorem piScalarRight_map_symm_single (T' : Type*) [CommRing T'] [Algebra T T']
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (φ : (ι → T) →ₐ[T] (κ → T)) (i : ι) (j : κ) :
    Algebra.TensorProduct.piScalarRight T T' T' κ
        (Algebra.TensorProduct.map (AlgHom.id T' T') φ
          ((Algebra.TensorProduct.piScalarRight T T' T' ι).symm (Pi.single i 1))) j =
      algebraMap T T' (φ (Pi.single i 1) j) := by
  have h : (Algebra.TensorProduct.piScalarRight T T' T' ι).symm (Pi.single i 1) =
      1 ⊗ₜ Pi.single i 1 := by
    rw [AlgEquiv.symm_apply_eq]
    ext k
    simp [Pi.single_apply]
  rw [h, Algebra.TensorProduct.map_tmul, AlgHom.id_apply,
    Algebra.TensorProduct.piScalarRight_tmul_apply, Algebra.algebraMap_eq_smul_one]

/-- The equalizer of two algebra maps between split algebras is finite étale. Over the component
of each atom of the Boolean algebra generated by the matrix entries, all entries become `0` or `1`,
and the equalizer is computed by `etale_and_finite_equalizer_of_entries`. -/
private theorem etale_and_finite_equalizer_pi {ι κ : Type*} [_root_.Finite ι] [_root_.Finite κ]
    (φ ψ : (ι → T) →ₐ[T] (κ → T)) :
    Algebra.Etale T (equalizer φ ψ) ∧ Module.Finite T (equalizer φ ψ) := by
  classical
  have := Fintype.ofFinite ι
  have := Fintype.ofFinite κ
  let a : Bool × ι × κ → T := fun x ↦ (bif x.1 then φ else ψ) (Pi.single x.2.1 1) x.2.2
  have ha (x : Bool × ι × κ) : IsIdempotentElem (a x) := by
    have hs : IsIdempotentElem (Pi.single x.2.1 1 : ι → T) := by
      rw [IsIdempotentElem, ← Pi.single_mul, mul_one]
    exact (hs.map (bif x.1 then φ else ψ)).map (Pi.evalRingHom (fun _ ↦ T) x.2.2)
  have hF := CompleteOrthogonalIdempotents.prod_ite ha
  suffices H : ∀ σ : Bool × ι × κ → Bool,
      let T' := T ⧸ Ideal.span {1 - ∏ x, if σ x then a x else 1 - a x}
      Algebra.Etale T' (T' ⊗[T] equalizer φ ψ) ∧ Module.Finite T' (T' ⊗[T] equalizer φ ψ) from
    ⟨Algebra.Etale.of_completeOrthogonalIdempotents hF fun σ ↦ (H σ).1,
      Module.Finite.of_completeOrthogonalIdempotents hF fun σ ↦ (H σ).2⟩
  intro σ T'
  -- In `T'` the atom becomes `1`, so every entry becomes `0` or `1` according to `σ`.
  have hT' (x : Bool × ι × κ) : algebraMap T T' (a x) = 0 ∨ algebraMap T T' (a x) = 1 := by
    have hfactor := congrArg (algebraMap T T') (ite_mul_prod_ite ha σ x)
    rw [map_mul, algebraMap_quotient_span_one_sub, mul_one] at hfactor
    split at hfactor
    · exact .inr hfactor
    · exact .inl (by simpa [sub_eq_self] using hfactor)
  have : IsLocalization.Away (∏ x, if σ x then a x else 1 - a x) T' :=
    IsLocalization.Away.quotient_of_isIdempotentElem (hF.idem σ)
  have : Module.Flat T T' :=
    IsLocalization.flat T' (Submonoid.powers (∏ x, if σ x then a x else 1 - a x))
  let eι := Algebra.TensorProduct.piScalarRight T T' T' ι
  let eκ := Algebra.TensorProduct.piScalarRight T T' T' κ
  let e := (AlgHom.tensorEqualizerEquiv T' T' φ ψ).trans
    (equalizerCongr eι eκ (Algebra.TensorProduct.map (AlgHom.id T' T') φ)
      (Algebra.TensorProduct.map (AlgHom.id T' T') ψ))
  obtain ⟨h₁, h₂⟩ := etale_and_finite_equalizer_of_entries
    ((eκ : (T' ⊗[T] (κ → T)) →ₐ[T'] (κ → T')).comp
      ((Algebra.TensorProduct.map (AlgHom.id T' T') φ).comp (eι.symm : (ι → T') →ₐ[T'] _)))
    ((eκ : (T' ⊗[T] (κ → T)) →ₐ[T'] (κ → T')).comp
      ((Algebra.TensorProduct.map (AlgHom.id T' T') ψ).comp (eι.symm : (ι → T') →ₐ[T'] _)))
    (fun i j ↦ by simpa [a, eι, eκ, piScalarRight_map_symm_single] using hT' (true, i, j))
    (fun i j ↦ by simpa [a, eι, eκ, piScalarRight_map_symm_single] using hT' (false, i, j))
  exact ⟨.of_equiv e.symm, .equiv e.symm.toLinearEquiv⟩

/-- The equalizer of two algebra maps between finite split algebras is finite étale. -/
private theorem etale_and_finite_equalizer_of_isFiniteSplit {A B : Type*} [CommRing A]
    [CommRing B] [Algebra T A] [Algebra T B] [Algebra.IsFiniteSplit T A]
    [Algebra.IsFiniteSplit T B] (f g : A →ₐ[T] B) :
    Algebra.Etale T (equalizer f g) ∧ Module.Finite T (equalizer f g) := by
  obtain ⟨m, ⟨eA⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun T A
  obtain ⟨n, ⟨eB⟩⟩ := Algebra.IsFiniteSplit.nonempty_algEquiv_fun T B
  let e := equalizerCongr eA eB f g
  obtain ⟨h₁, h₂⟩ := etale_and_finite_equalizer_pi
    ((eB : B →ₐ[T] (Fin n → T)).comp (f.comp (eA.symm : (Fin m → T) →ₐ[T] A)))
    ((eB : B →ₐ[T] (Fin n → T)).comp (g.comp (eA.symm : (Fin m → T) →ₐ[T] A)))
  exact ⟨.of_equiv e.symm, .equiv e.symm.toLinearEquiv⟩

end Split

/-- The equalizer of two algebra maps between finite étale algebras of constant ranks is finite
étale. Both algebras split after a faithfully flat finite étale base change
(`Algebra.IsFiniteSplit.exists_tensorProduct_of_etale`), flat base change commutes with
equalizers (`AlgHom.tensorEqualizerEquiv`), and finite étaleness descends. -/
private theorem etale_and_finite_equalizer_of_rankAtStalk_eq {R A B : Type u} [CommRing R]
    [CommRing A] [CommRing B] [Algebra R A] [Algebra R B] [Algebra.Etale R A] [Module.Finite R A]
    [Algebra.Etale R B] [Module.Finite R B] {m n : ℕ} (hA : Module.rankAtStalk (R := R) A = m)
    (hB : Module.rankAtStalk (R := R) B = n) (f g : A →ₐ[R] B) :
    Algebra.Etale R (equalizer f g) ∧ Module.Finite R (equalizer f g) := by
  obtain ⟨T₁, _, _, _, _, _, _⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hA
  have hB₁ : Module.rankAtStalk (R := T₁) (T₁ ⊗[R] B) = n := by
    ext p
    rw [Module.rankAtStalk_baseChange, hB, Pi.natCast_apply, Pi.natCast_apply]
  obtain ⟨T₂, _, _, _, _, _, _⟩ := Algebra.IsFiniteSplit.exists_tensorProduct_of_etale hB₁
  let : Algebra R T₂ := ((algebraMap T₁ T₂).comp (algebraMap R T₁)).toAlgebra
  have : IsScalarTower R T₁ T₂ := .of_algebraMap_eq' rfl
  have : Module.FaithfullyFlat R T₂ := .trans R T₁ T₂
  have : Algebra.IsFiniteSplit T₂ (T₂ ⊗[R] A) :=
    .of_algEquiv (Algebra.TensorProduct.cancelBaseChange R T₁ T₂ T₂ A)
  have : Algebra.IsFiniteSplit T₂ (T₂ ⊗[R] B) :=
    .of_algEquiv (Algebra.TensorProduct.cancelBaseChange R T₁ T₂ T₂ B)
  let e := AlgHom.tensorEqualizerEquiv T₂ T₂ f g
  obtain ⟨h₁, h₂⟩ := etale_and_finite_equalizer_of_isFiniteSplit
    (Algebra.TensorProduct.map (AlgHom.id T₂ T₂) f) (Algebra.TensorProduct.map (AlgHom.id T₂ T₂) g)
  have : Algebra.Etale T₂ (T₂ ⊗[R] equalizer f g) := .of_equiv e.symm
  have : Module.Finite T₂ (T₂ ⊗[R] equalizer f g) := .equiv e.symm.toLinearEquiv
  exact ⟨.of_etale_tensorProduct_of_faithfullyFlat T₂,
    .of_finite_tensorProduct_of_faithfullyFlat T₂⟩

/-- Let the loci where a finite flat module `M` has rank `k ≤ N` be the basic open sets of `ε k`.
If whether `ε k` is a unit at a prime of `T'` does not depend on the prime, then the base change of
`M` to `T'` has constant rank. -/
private theorem exists_rankAtStalk_tensorProduct_eq {R T' M : Type*} [CommRing R] [CommRing T']
    [Algebra R T'] [AddCommGroup M] [Module R M] [Module.Flat R M] [Module.Finite R M] {N : ℕ}
    (ε : Fin (N + 1) → R) (P : Fin (N + 1) → Prop)
    (hM : ∀ p, Module.rankAtStalk (R := R) M p ≤ N)
    (hε : ∀ k, (PrimeSpectrum.basicOpen (ε k) : Set (PrimeSpectrum R)) =
      Module.rankAtStalk (R := R) M ⁻¹' {(k : ℕ)})
    (hP : ∀ (q : PrimeSpectrum T') k, ε k ∉ (q.comap (algebraMap R T')).asIdeal ↔ P k) :
    ∃ m : ℕ, Module.rankAtStalk (R := T') (T' ⊗[R] M) = m := by
  classical
  refine ⟨if h : ∃ k, P k then h.choose else 0, funext fun q ↦ ?_⟩
  rw [Module.rankAtStalk_baseChange, Pi.natCast_apply]
  have hmem (k : Fin (N + 1)) : P k ↔ Module.rankAtStalk M (q.comap (algebraMap R T')) = k := by
    rw [← hP q k]
    simpa [PrimeSpectrum.mem_basicOpen] using congrArg (q.comap (algebraMap R T') ∈ ·) (hε k)
  have hex : ∃ k, P k :=
    ⟨⟨_, Nat.lt_succ_of_le (hM (q.comap (algebraMap R T')))⟩, (hmem _).mpr rfl⟩
  simp only [hex, ↓reduceDIte]
  exact (hmem _).mp hex.choose_spec

/-- The equalizer of two algebra maps between finite étale algebras is finite étale. The ranks of
the two algebras are locally constant, so the atoms of the idempotents cutting out their fibres
decompose the base into components over which both ranks are constant. -/
private theorem etale_and_finite_equalizer {R A B : Type u} [CommRing R] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra R B] [Algebra.Etale R A] [Module.Finite R A] [Algebra.Etale R B]
    [Module.Finite R B] (f g : A →ₐ[R] B) :
    Algebra.Etale R (equalizer f g) ∧ Module.Finite R (equalizer f g) := by
  classical
  have : Module.FinitePresentation R A := .of_finite_of_finitePresentation R A
  have : Module.FinitePresentation R B := .of_finite_of_finitePresentation R B
  obtain ⟨N, hNA, hNB⟩ : ∃ N, (∀ p, Module.rankAtStalk (R := R) A p ≤ N) ∧
      ∀ p, Module.rankAtStalk (R := R) B p ≤ N := by
    obtain ⟨NA, hNA⟩ :=
      (Module.isLocallyConstant_rankAtStalk (R := R) (M := A)).range_finite.bddAbove
    obtain ⟨NB, hNB⟩ :=
      (Module.isLocallyConstant_rankAtStalk (R := R) (M := B)).range_finite.bddAbove
    exact ⟨max NA NB, fun p ↦ (hNA ⟨p, rfl⟩).trans (le_max_left _ _),
      fun p ↦ (hNB ⟨p, rfl⟩).trans (le_max_right _ _)⟩
  choose εA hεA hεA' using fun k : Fin (N + 1) ↦
    Module.exists_isIdempotentElem_basicOpen_eq_preimage_rankAtStalk (R := R) A k
  choose εB hεB hεB' using fun k : Fin (N + 1) ↦
    Module.exists_isIdempotentElem_basicOpen_eq_preimage_rankAtStalk (R := R) B k
  let a : Fin (N + 1) ⊕ Fin (N + 1) → R := Sum.elim εA εB
  have ha (x : Fin (N + 1) ⊕ Fin (N + 1)) : IsIdempotentElem (a x) := by
    cases x
    · exact hεA _
    · exact hεB _
  have hF := CompleteOrthogonalIdempotents.prod_ite ha
  suffices H : ∀ σ : Fin (N + 1) ⊕ Fin (N + 1) → Bool,
      let T' := R ⧸ Ideal.span {1 - ∏ x, if σ x then a x else 1 - a x}
      Algebra.Etale T' (T' ⊗[R] equalizer f g) ∧ Module.Finite T' (T' ⊗[R] equalizer f g) from
    ⟨Algebra.Etale.of_completeOrthogonalIdempotents hF fun σ ↦ (H σ).1,
      Module.Finite.of_completeOrthogonalIdempotents hF fun σ ↦ (H σ).2⟩
  intro σ T'
  -- Every prime of `T'` lies over the component of the atom, where the ranks of `A` and `B` are
  -- read off from the atom.
  have hσ (q : PrimeSpectrum T') : ∀ x, a x ∉ (q.comap (algebraMap R T')).asIdeal ↔ σ x := by
    refine notMem_iff_of_one_sub_prod_ite_mem ha σ ?_
    rw [PrimeSpectrum.comap_asIdeal, Ideal.mem_comap, map_sub, map_one,
      algebraMap_quotient_span_one_sub, sub_self]
    exact q.asIdeal.zero_mem
  obtain ⟨m, hm⟩ := exists_rankAtStalk_tensorProduct_eq (T' := T') εA (fun k ↦ σ (.inl k)) hNA
    hεA' fun q k ↦ hσ q (.inl k)
  obtain ⟨n, hn⟩ := exists_rankAtStalk_tensorProduct_eq (T' := T') εB (fun k ↦ σ (.inr k)) hNB
    hεB' fun q k ↦ hσ q (.inr k)
  have : IsLocalization.Away (∏ x, if σ x then a x else 1 - a x) T' :=
    IsLocalization.Away.quotient_of_isIdempotentElem (hF.idem σ)
  have : Module.Flat R T' :=
    IsLocalization.flat T' (Submonoid.powers (∏ x, if σ x then a x else 1 - a x))
  let e := AlgHom.tensorEqualizerEquiv T' T' f g
  obtain ⟨h₁, h₂⟩ := etale_and_finite_equalizer_of_rankAtStalk_eq hm hn
    (Algebra.TensorProduct.map (AlgHom.id T' T') f) (Algebra.TensorProduct.map (AlgHom.id T' T') g)
  exact ⟨.of_equiv e.symm, .equiv e.symm.toLinearEquiv⟩

section

variable {R A B : Type u} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
  [Algebra.Etale R A] [Module.Finite R A] [Algebra.Etale R B] [Module.Finite R B]

/-- **The equalizer of two algebra maps between finite étale algebras is étale.** Geometrically,
the affine coequalizer of two morphisms between finite étale `Spec R`-schemes is finite étale. -/
instance etale_equalizer (f g : A →ₐ[R] B) : Algebra.Etale R (equalizer f g) :=
  (etale_and_finite_equalizer f g).1

/-- The equalizer of two algebra maps between finite étale algebras is a finite module. -/
instance finite_equalizer (f g : A →ₐ[R] B) : Module.Finite R (equalizer f g) :=
  (etale_and_finite_equalizer f g).2

end

end AlgHom

namespace FixedPoints

variable {R S : Type u} [CommRing R] [CommRing S] [Algebra R S] (G : Type*) [Monoid G]
  [MulSemiringAction G S] [SMulCommClass G R S]

/-- For an enumeration `σ` of a finite monoid `G`, the invariant subalgebra is the equalizer of the
diagonal map `S → (Fin n → S)` and `s ↦ (σ i • s)ᵢ`. -/
private theorem subalgebra_eq_equalizer {n : ℕ} (σ : Fin n ≃ G) :
    FixedPoints.subalgebra R S G = AlgHom.equalizer (AlgHom.pi fun _ ↦ AlgHom.id R S)
      (AlgHom.pi fun i ↦ MulSemiringAction.toAlgHom R S (σ i)) := by
  ext s
  simp only [FixedPoints.mem_subalgebra, AlgHom.mem_equalizer, funext_iff, AlgHom.pi_apply,
    AlgHom.id_apply, MulSemiringAction.toAlgHom_apply, σ.forall_congr_left, Equiv.apply_symm_apply]
  exact forall_congr' fun _ ↦ eq_comm

variable [Algebra.Etale R S] [Module.Finite R S] [Finite G]

/-- **The invariants of a finite étale algebra under a finite monoid of algebra endomorphisms form
a finite étale algebra.** Geometrically, the invariant quotient `Spec Sᴳ` of a finite étale
`Spec R`-scheme `Spec S` by a finite group is again finite étale. -/
instance etale_subalgebra : Algebra.Etale R (FixedPoints.subalgebra R S G) := by
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin G
  rw [subalgebra_eq_equalizer G σ.symm]
  infer_instance

/-- The invariants of a finite étale algebra under a finite monoid of algebra endomorphisms form a
finite module. -/
instance finite_subalgebra : Module.Finite R (FixedPoints.subalgebra R S G) := by
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin G
  rw [subalgebra_eq_equalizer G σ.symm]
  infer_instance

end FixedPoints
